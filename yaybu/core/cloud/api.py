
from libcloud.compute.types import Provider as ComputeProvider
from libcloud.storage.types import Provider as StorageProvider
from libcloud.dns.types import Provider as DNSProvider

from libcloud.compute.providers import get_driver as get_compute_driver
from libcloud.storage.providers import get_driver as get_storage_driver
from libcloud.dns.providers import get_driver as get_dns_driver

from libcloud.compute.deployment import MultiStepDeployment, ScriptDeployment, SSHKeyDeployment
import libcloud.security
from libcloud.common.types import LibcloudError

from boto.route53.connection import Route53Connection
from boto.route53.record import ResourceRecordSets
from boto.route53.record import Record

import os
import uuid
import logging
import yaml
import StringIO
import datetime
import collections
import time

from yaybu.core.util import memoized
from yaybu.core import remote

libcloud.security.VERIFY_SSL_CERT = True

logger = logging.getLogger(__name__)

max_version = 1

class Route53Zone:
    
    def __init__(self, connection, zone):
        self.connection = connection
        self.id = zone['Id'].replace('/hostedzone/', '')
        
    def create_record(self, name, data):
        logger.debug("Creating record")
        changes = ResourceRecordSets(self.connection,
                                     self.id,
                                     "")
        change = changes.add_change("CREATE", name, 'A', 60)
        change.add_value(data)
        status = changes.commit()['ChangeResourceRecordSetsResponse']['ChangeInfo']
        logger.debug("Status response is %r" % status)
        
class Route53:
    
    """ Our driver that handles route53 using boto """
    
    def __init__(self, key, secret):
        self.connection = Route53Connection(key, secret)
        
    def create_zone(self, domain):
        zone = self.connection.create_hosted_zone(domain)
        logger.debug("Zone is %r" % zone)
        zone = zone['CreateHostedZoneResponse']['HostedZone']
        return Route53Zone(self.connection, zone)  

class Cloud(object):

    """ Adapter of a cloud that provides access to runtime functionality. """

    def __init__(self, compute_provider, storage_provider, dns_provider, args):
        self.compute_provider = compute_provider
        self.storage_provider = storage_provider
        self.dns_provider = dns_provider
        self.args = args

    @property
    @memoized
    def compute(self):
        provider = getattr(ComputeProvider, self.compute_provider)
        driver_class = get_compute_driver(provider)
        return driver_class(**self.args)
    
    @property
    @memoized
    def storage(self):
        provider = getattr(StorageProvider, self.storage_provider)
        driver_class = get_storage_driver(provider)
        return driver_class(**self.args)
    
    @property
    @memoized
    def dns(self):
        if self.dns_provider == "route53":
            return Route53(**self.args)
        else:
            provider = getattr(DNSProvider, self.dns_provider)
            driver_class = get_dns_driver(provider)
            return driver_class(**self.args)

    @property
    @memoized
    def images(self):
        return dict((i.id, i) for i in self.compute.list_images())

    @property
    @memoized
    def sizes(self):
        return dict((s.id, s) for s in self.compute.list_sizes())

    @property
    def nodes(self):
        return dict((n.name, n) for n in self.compute.list_nodes())

    def get_container(self, name):
        try:
            container = self.storage.get_container(container_name=name)
        except ContainerDoesNotExistError:
            container = self.storage.create_container(container_name=name)
        return container
            
    def create_node(self, name, image, size, keypair):
        """ This creates a physical node based on our node record. """
        for tries in range(10):
            logger.debug("Creating node %r with image %r, size %r and keypair %r" % (
                name, image, size, keypair))
            node = self.compute.create_node(
                name=name,
                image=self.images[image],
                size=self.sizes[size],
                ex_keyname=keypair)
            logger.debug("Waiting for node %r to start" % (name, ))
            ## TODO: wrap this in a try/except block and terminate
            ## and recreate the node if this fails
            try:
                self.compute._wait_until_running(node, timeout=60)
            except LibcloudError:
                logger.warning("Node did not start before timeout. retrying.")
                node.destroy()
                continue
            if not name in self.nodes:
                logger.debug("Naming fail for new node. retrying.")
                node.destroy()
                continue
            logger.debug("Node %r running" % (name, ))
            return self.nodes[name]
        logger.error("Unable to create node successfully. giving up.")
        raise IOError()

    def update_record(self, ip, zone, name):
        """ Create an A record for the ip/dns pairing """
        z = self.dns.create_zone(domain=zone)
        record = z.create_record(name=name, data=ip)
        loggger.info("Created record for %r -> %r" % (name, ip))
        
.. _compute:

=================
Compute instances
=================

The ``Compute`` part can be used to create and destroy services in various
cloud services supported by libcloud as well as various local VM tools.

Creating a simple compute node will look something like this::

    new Compute as server:
        name: test123456

        driver:
            id: BIGV
            key: yourusername
            secret: yourpassword
            account: youraccountname

        image: precise

        user: root
        password: aez5Eep4

In this example we are creating a server via `BigV <http://www.bigv.io/>`_, but
because our cloud support is underpinned by libcloud we support many hosting
providers.


Options
=======

Any compute instances you create must have a unique ``name``. This lets yaybu keep track of it between ``yaybu apply`` invocations.

Use the ``driver`` argument to configure a libcloud driver for your hosting service. Specific driver sub arguments are discussed in the sections below.

You can choose an base image using the ``image`` argument. For the common case an image id is enough::

    new Compute as server:
        image: ami-f7445d83

You can choose an instance ``size`` by passing a size name::

    new Compute as server:
        size: t1.micro

Some servers don't have the concept of size but you can control the resources assigned in a more granular way::

    new Computer as server:
        size:
            processors: 5

See the driver specific options below for more information on what tweaks you can pass to a backend.

You must choose a ``username`` that can be used to log in with.

If you provide a ``public_key`` file and are using a driver that supports it Yaybu will automatically load it into the created instance to enable key based authentication.

If you provide a ``password`` and the backend supports it then Yaybu will automatically set the account password for the newly created instance.

The ``Compute`` part does not look at the ``private_key`` attribute, but as it is common to use the ``Compute`` part directly with a ``Provisioner`` part, which does check for it, you will often see it specified::

    new Provisioner as vm1:
        new Compute as server:
            private_key: path/to/privatekey


Supported services
==================

BigV
----

Our `BigV <http://www.bigv.io/>`_ support is implemented via `the libcloud 
library <https://github.com/apache/libcloud>`_ but is currently residing in
the Yaybu codebase. As you can set the password for an instance when it is
created there is no preparation to do to create a bigv instance, other than
creating a bigv account.

Your ``Yaybufile`` looks like this::

    new Provisioner as vm1:
        new Compute as server:
            name: test123456

            driver:
                id: BIGV
                key: yourusername
                secret: yourpassword
                account: youraccountname

            image: precise

            user: root
            password: aez5Eep4

        resources:
          - Package:
              name: git-core

This example will create a new vm called ``test123456``. You will be able to
log in as root using the password ``aez5Eep4`` (though you should use ``pwgen``
to come up with something better).


EC2
---

Provisioning of AWS instances is supported out of the box using libcloud.
You will need to have set up an SSH key in the Amazon control panel and either
have the path to the private part of that key or have added it to your
ssh-agent.

You'll need something like this in your ``Yaybufile``::

    new Compute as server:
        name: myappserver

        driver:
            id: EC2_EU_WEST
            key: mykey
            secret: mysecret

        size: t1.micro
        image: ami-4f504f3b

        user: ubuntu
        ex_keyname: mykey
        private_key: mykey.pem


``ex_keyname`` is the name of the SSH key pair in the amazon console.
``private_key`` is the corresponding private key.

We recently merged a patch upstream to do away with ``ex_keyname``. In future Yaybu will be able to automatically upload a ``public_key`` for you in the same way it can for other backends.


VMWare
------

You'll need a copy of VMWare Workstation, VMWare Fusion or VMWare Player.
You'll need a base image to use. My checklist when creating mine is:

* Is ``openssh-server`` installed?
* Is there a user with passphraseless sudo access to root?
* Have I deleted the /etc/udev/rules.d/70-persistent-net.rules?

When you are done, shut down the VM and get the path to its VMX file.

Now your ``Yaybufile`` looks like this::

    new Compute as server:
        name: mytest vm

        driver:
            id: VMWARE

        image:
            id: ~/vmware/ubuntu/ubuntu.vmx

        user: ubuntu

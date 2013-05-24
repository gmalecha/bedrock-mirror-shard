The BEDROCK Coq library (MirrorShard port)

Mostly automated verification of higher-order programs with
higher-order separation logic, with a small trusted code base
http://plv.csail.mit.edu/bedrock/


This release requires Coq 8.4 (final released version).

Building
--------
Download coq-ext-lib from:
  
  https://github.com/coq-ext-lib/coq-ext-lib.git

build it, and create a symbolic link called coq-ext-lib to that
directory.

Download MirrorShard from:

  https://github.com/gmalecha/mirror-shard

build it, and create a symbolic link called mirror-shard to that
directory.

Then, run one of the following:

   make native

or

   make ltac

to select whether to use the OCaml or Ltac reification code,
respectively.  By default, you get the Ltac version, which is _much_
slower (i.e., adds hours to the time to build the library and all
examples serially), but avoids the need to load a plugin into Coq,
which can be tricky to do on some platforms.

Then, just run:

   make

and go take a break while it runs for an hour or so (if you're lucky
enough to have a new-ish machine). ;) Using the '-j' switch for
parallel build is highly recommended.

Also see the 'examples' directory and its README.


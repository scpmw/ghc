
How To Build and Use
===================

Requirements
------------

* A [Linux](http://kernel.org) distribution - preferably new enough to have perf-event, for getting nice
  low-level profiles.

* [LLVM](http://llvm.org) installed - because that's currently the
  only way to write debug meta data.

* `libdwarf-dev` (or similar) installed - because that's the only way we
  *can currently read* debug data.

Note the installation will gracefully fail if any of these are not
met, and just compile a GHC without the respective support enabled.

Getting GHC
-----------

First get a GHC source tree and a set of libraries compatible to GHC
7.6:

     $ git clone -b ghc-7.6 http://darcs.haskell.org/ghc.git ghc-git 
     $ cd ghc-git
     $ ./sync-all get

Then fetch the profiling GHC branch:

     $ git remote add profiling http://github.com/scpmw/ghc
     $ git fetch profiling
     $ git checkout profiling-7.6 remotes/profiling/profiling-7.6

Make a configuration:

     $ cat > mk/build.mk
     GhcLibWays      = v
     SRC_HC_OPTS     = -O -H64m
     GhcStage1HcOpts = -O -fasm
     GhcStage2HcOpts = -O2 -fllvm
     GhcLibHcOpts    = -O2 -fllvm
     SplitObjs          = NO
     HADDOCK_DOCS       = NO
     BUILD_DOCBOOK_HTML = NO
     BUILD_DOCBOOK_PS   = NO
     BUILD_DOCBOOK_PDF  = NO
      
Build and install:

      $ perl boot
      $ ./configure --prefix=$GHC_INSTALL_PREFIX
      $ make -j4
      $ make install

You should probably get a cup of coffee at this point, as GHC can take
significant amounts of time to build. Change the `-j` parameter to
match your machine's core count.

After installation, you should be able to put `$GHC_INSTALL_PREFIX`
into the path and use the freshly compiled GHC to compile your program
with profiling enabled:

      $ ghc myProgram.hs -O2 -fllvm -rtsopts -eventlog
      $ ./myProgram +RTS -ls -E -RTS

Where `-ls` enables the eventlog output, and `-E` enables
`perf_event`-based instruction profiling.

Getting ThreadScope
-------------------

Get the source packages here:

* [ghc-events-pmw-0.4.0.0.tar.gz](http://www.personal.leeds.ac.uk/~scpmw/ghc-events-pmw-0.4.0.0.tar.gz)
* [threadscope-pmw-0.2.1.tar.gz](http://www.personal.leeds.ac.uk/~scpmw/threadscope-pmw-0.2.1.tar.gz)

After installing the GTK bindings as well as these packages, you
should be able to view generated profiles using `threadscope-pmw`:

      $ threadscope-pmw myProgram.eventlog

Hints
-----

If you followed the above instructions for building GHC, you should
have libraries will full debug information. Hoever, ThreadScope won't
know where to find the sources unless we add the GHC source to the
search directories:

      $ threadscope-pmw myProgram.eventlog -d $GHC_INSTALL_PREFIX

Feedback
--------

When (!) you run into problems, feel free to contact me at (scpmw@leeds.ac.uk)[mailto:scpmw@leeds.ac.uk].

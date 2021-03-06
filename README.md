How To Build and Use
===================

Requirements
------------

* A [Linux](http://kernel.org) distribution - preferably new enough to have perf-event, for getting nice
  low-level profiles.

* `libelf-dev` and `libdwarf-dev` (or similar) installed - because
  that's how the runtime data reads DWARF. Note that
  if you compile GHC using dynamic linking (the default) you need
  a version of `libdwarf` that was compiled with `--enable-shared`.
  Getting there might involve compiling `libdwarf` manually. As a
  rule of thumb, once your system has a `libdwarf.so` file installed,
  it should work.

Note the installation will gracefully fail if any of these are not
met, and just compile a GHC without the respective support enabled.

Getting GHC
-----------

First get a GHC source tree and a set of libraries compatible to GHC
7.6:

     $ git clone -b profiling-ncg http://github.com/scpmw/ghc ghc-git 
     $ cd ghc-git
     $ ./sync-all -r http://git.haskell.org/ get

Make a configuration:

     $ cat > mk/build.mk
     GhcLibWays      = v dyn
     SRC_HC_OPTS     = -O -H64m
     GhcStage1HcOpts = -O -fasm
     GhcStage2HcOpts = -O2 -fasm
     GhcLibHcOpts    = -O2
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

      $ ghc myProgram.hs -O2 -rtsopts -eventlog
      $ ./myProgram +RTS -ls -E

Where `-ls` enables the eventlog output, and `-E` enables
`perf_event`-based instruction profiling.

Getting ThreadScope
-------------------

You will need custom versions of ghc-events & ThreadScope:

     $ git clone http://github.com/scpmw/ghc-events ghc-events
     $ (cd ghc-events; cabal install)
     $ git clone http://github.com/scpmw/ThreadScope ThreadScope
     $ (cd ThreadScope; cabal install)

After installing the GTK bindings as well as these packages, you
should be able to view generated profiles using `threadscope-pmw`:

      $ threadscope-pmw myProgram.eventlog

Hints and Known Problems
------------------------

* If you followed the above instructions for building GHC, you should
  have libraries will full debug information. However, ThreadScope
  won't know where to find the sources unless we add the GHC source to
  the search directories:

      $ threadscope-pmw myProgram.eventlog -d $GHC_INSTALL_PREFIX

* If your ThreadScope installation crashes when clicking on the left
  side bar, your `gtksourceview2` installation still has a bug that
  makes it impossible to react to these kinds of events without
  causing a crash. You can find a patch to `gtksourceview2` that
  corrects this problem attached to the bug report:

  http://hackage.haskell.org/trac/gtk2hs/ticket/1252

* If the program complied with the custom GHC refuses to accept the
  `-E` command line option, the `perf_event` interface is not
  available or was not detected properly.

  Check that you have a compatible Linux version, and that the
  configuration process correctly set `GhcRtsWithPerfEvent = YES`

* In the case that you don't see any sources or Core in ThreadScope
  even though there are "Instruction pointer sample" entries in the
  event log, `libdwarf` was probably not found when configuring the
  GHC build.

  Check the installation and that `GhcRtsWithDwarf = YES` is set in
  `mk/config.mk`.

Feedback
--------

Once you have run into problems - please contact me at
scpmw@leeds.ac.uk.

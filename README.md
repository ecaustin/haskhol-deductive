# haskhol-deductive
HaskHOL libraries for higher level deductive reasoning. See haskhol.org for more information.
As a fair warning, this release is relatively stable, but heavily undocumented.

Note:  Running plain `cabal build` has a tendency to cause simultaneous splicing of template haskell expressions.  This can create some resource locking errors during compilation due to the way HaskHOL currently utilizes acid-state and shelly.  To fix this problem, build with the -j1 flag, e.g. `cabal build -j1`.

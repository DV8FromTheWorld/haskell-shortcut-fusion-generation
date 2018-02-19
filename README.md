# haskell-shortcut-fusion-generation

This program takes in a file in containing 1 GADT declaration and will output a generated fold and build function similar to an ADT's Deriving Foldable for the GADT.

### Setup
 1) Download The Haskell Platform (ghc, cabal, etc): https://www.haskell.org/platform/
 2) Update the Cabal package list:  Run `cabal update`
 3) Clone the project to a local folder
 4) Install the project and its dependencies. Run `cabal install`.
 This will install all external dependencies needed and compile the project, installing it to a PATH discoverable location.
 
With the project configured and installed, you can now run it from anywhere on your commandline.

### Use
`shortcut-fusion-gen infile outfile`

The infile must be a valid text file containing *only* a GADT declaration. You can find a few examples in the `tests/` directory.
Currently, the outfile is used for nothing. The generation is placed in the console.

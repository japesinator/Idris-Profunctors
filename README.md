Idris Profunctors
=================

This is a profunctor library for idris based off the excellent [Haskell Profunctors](https://github.com/ekmett/profunctors) package from Edward Kmett.  Contributions, bug reports, and feature requests are welcome.

Contains
--------

  * Profunctors (including verified versions)

  * Various Profunctor/Functor transformations

  * Lenses

  * Isomorphisms

  * Prisms

Installation
------------

Run `idris --install profunctors.ipkg` from inside this directory, and then if
you want to use it with anything, invoke idris with `-p profunctors` (i.e.
`idris -p profunctors hack_the_planet.idr`)

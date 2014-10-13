Project structure
================

The project consists of four parts:
 * language
 * interpreter
 * scade2lama
 * lamaSMT
The first contains the parser, type checker and dependency checker for the LAMA
language.
There is an interpreter for LAMA in the directory of the same name, so that one
can run simulations.
Next, we have the translator from SCADE to LAMA, to be found in "scade2lama".
Last but not least, in lamaSMT the actual verfication of LAMA programs using SMT
is implemented.

Installation and Dependencies
==============

It is recommended to use cabal for installation.
The "language" project does not require any special libraries, only alex and
happy need to be installed.
So after that, a simple "cabal install" in the "language" directory should
suffice.
All other subprojects require "language" to be installed.
The installation of the interpreter is optional, usually it is not required.
The "scade2lama" subproject requires the library "language-scade" to be
installed, which is not on hackage.
It can be found at https://github.com/hguenther/language-scade.
Finally, the "lamaSMT" project requires additionally smtlib2 to be installed.
This is located at https://github.com/hguenther/smtlib2.
The last known version to work with this project is
https://github.com/hguenther/smtlib2/tree/58ad9aa7e1c0ef2ba460667d03461e023c0a8a76,
though it can be that more recent version work as well.

Running
========

After installation, one might actually want to use the project.
It is recommended to add the cabal binary directory (e.g., ~/.cabal/bin) to the
PATH, to be able to easily run the installed programs (this might even be
necessary during the installation, to run alex and happy).

Having done this, the interpreter can be run with the command "lamai", the SCADE
translator with "scade2lama" and the verification tool with "lamasmt".
The latter requires z3 (https://z3.codeplex.com/) to installed and available in
the PATH.

Development
===========

The project development follows the guidelines for git projects at
http://nvie.com/posts/a-successful-git-branching-model/.

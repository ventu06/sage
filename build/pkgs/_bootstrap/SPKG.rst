_bootstrap: Represents system packages required for running the top-level bootstrap script
==========================================================================================

Description
-----------

This optional script package represents the requirements (system packages)
that are needed in addition to those represented by the ``_prereq`` package
in order to run the top-level ``bootstrap`` script.

Namely, the following standard tools must be installed on your computer:

- **liblzma/xz**: XZ Utils, the free general-purpose data compression software
  with a high compression ratio.
- **python**: Python 3.12 or later; it needs to have the development headers and the following standard
  modules available: sqlite3, ctypes, math, hashlib, socket, ssl, ensurepip, zlib

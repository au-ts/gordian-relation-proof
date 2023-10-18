Relation proof
==============

This work is part of the microkit verification project.

This repository contains the proof that the relation between the microkit state
machine is maintained with kernel projection, in SMT.

The entire proof is in the file `spec.smt2`.

The spec is written for MCS kernel (recv and replyrecv) takes reply_cptr
arguments (careful: the C code in this repository is non-MCS).


It is a manual translation of the specification written in Haskell as part the
NCSC deliverables that can be found at https://github.com/zaklogician/nc0323
(private repository) under july/spec/app. Email Mathieu to get a clone, if you
don't have access to it.

The Haskell spec in this repository contains some of my modifications and
comments. It is *not* a reference. The SMT is the reference.

Running the proof
=================

Takes about 15 seconds.

    $ python3 run-proofs.py

This program will ensure that each proof produces the expected result (sat or
unsat).

Resources
=========

@Rob: you most likely want to read `notes.txt`

- http://smtlib.cs.uiowa.edu/
- https://www.pm.inf.ethz.ch/education/courses/program-verification.html
- documentation folder (email Mathieu)




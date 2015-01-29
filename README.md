fingertrees
===========

Random assortment of finger tree stuff based on [Hinze and Paterson's
paper](http://staff.city.ac.uk/~ross/papers/FingerTree.html), mostly
to learn about them for a talk.

Most of the work here was on interval trees since I was using them for
work.

Unfortunately my code for sequences is much slower than the standard
library's Data.Sequence module; their structure is restricted to using
machine words as keys ("summary values") and consequently doesn't have
to dereference a pointer every time it accesses a key.  I haven't
looked carefully at their code to see whether they are doing anything
else more cleverly than I am to speed things up.

The future of this code is more playing with interval trees and
code-generating versions specialized to particular interval types
(`Double`, `Word64`, `UTCTime` etc.).  I am also partway through
building a type-class-based interface to make working with data of
various types with the same interval domain easier.

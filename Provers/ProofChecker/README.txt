This directory contains a proof checker for the Metaslang logic, written in
Metaslang. The Metaslang logic is formally defined in the document "The Logic
of Metaslang", by Alessandro Coglio, available at Specware4/DevDoc/logic.pdf.
Read that document first and refer to it while reading the .sw files in this
directory. The document is referred to as "LD" (for "Logic Document") in the
comments in the files.

The subdirectory Libs contains units that should belong to an external
library, because they are not specific to the proof checker. They are all
collected together in spec `MyBase' (under the Libs subdirectory) and they are
meant to constitute an extension of the base libraries for the proof checker.
For this reason, spec `MyBase' is systematically imported in every spec that
would not otherwise import any other spec, which guarantees `MyBase' to be
available in every spec.

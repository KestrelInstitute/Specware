This directory contains a proof checker for the Metaslang logic, written in
Metaslang. The Metaslang logic is formally defined in the document "The Logic
of Metaslang", by Alessandro Coglio, available at Specware4/DevDoc/logic.pdf.
Read that document first and refer to it while reading the .sw files in this
directory. The document is referred to as "LD" (for "Logic Document") in the
comments in the files.

The notion of provability in the Metaslang logic is defined in spec
`Provability'. The top-level proof checker spec is `Check'. The statement of
the correctness of the proof checker w.r.t. the notion of provability is
stated in spec `CheckCorrectness'. The executable version of the proof checker
is spec `CheckExecutable'. Spec `Test' is used to test the proof checked from
the Specware Shell. All other specs and morphisms in this directory are
auxiliary to the main specs just described.

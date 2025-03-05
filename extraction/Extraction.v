From LambCal Require Import Lambda.

(* Extraction config *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Coq.extraction.Extraction.
Extraction Language OCaml.
Set Extraction Output Directory "lambda/lib".

Separate Extraction Lambda.get_type Lambda.type_to_string.
  

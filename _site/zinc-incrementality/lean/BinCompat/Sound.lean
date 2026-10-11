import BinCompat.Fixed

/-!
# The corrected rules are sound on the space

Every well-formed single edit of `base1` and `base2` (`BinCompat.Edits`) that the corrected rules
do not report leaves every client of `spaceB` that linked still linking. Kernel `decide`: per base
and class, the unreported variants are pinned and the rest shown sound without running a client;
then each unreported edit is run against all of `spaceB` (about 15 s and 6 GB each). So this
module is not imported by `BinCompat` and is built on demand: `lake build BinCompat.Sound` (about
half an hour). This is
enumeration as testing (`DESIGN-spec.md`), not a proof for all libraries.
-/

namespace BinCompat

open Jvm Jvm.Catalogue Jvm.Clients

/-! ## The checks -/

example : (List.range (nVariants 1 .A)).all (fun i => (unreported 1 .A).contains i || sound 1 .A i) = true := by
  decide +kernel
example : unreported 1 .A = [5, 6, 7, 42, 43, 44, 45, 46, 47, 48, 49, 58, 59, 60, 61, 62, 63, 64, 65] := by decide +kernel
example : (List.range (nVariants 1 .B)).all (fun i => (unreported 1 .B).contains i || sound 1 .B i) = true := by
  decide +kernel
example : unreported 1 .B = [5, 6, 7, 9, 42, 43, 44, 45, 46, 47, 48, 49, 58, 59, 60, 61, 62, 63, 64, 65, 75] := by decide +kernel
example : (List.range (nVariants 1 .I)).all (fun i => (unreported 1 .I).contains i || sound 1 .I i) = true := by
  decide +kernel
example : unreported 1 .I = [0, 7, 43, 46, 59, 62] := by decide +kernel
example : (List.range (nVariants 1 .J)).all (fun i => (unreported 1 .J).contains i || sound 1 .J i) = true := by
  decide +kernel
example : unreported 1 .J = [0, 6, 13, 26, 29, 43, 46, 59, 62] := by decide +kernel
example : (List.range (nVariants 2 .A)).all (fun i => (unreported 2 .A).contains i || sound 2 .A i) = true := by
  decide +kernel
example : unreported 2 .A = [5, 6, 7, 42, 43, 44, 45, 46, 47, 48, 49, 58, 59, 60, 61, 62, 63, 64, 65] := by decide +kernel
example : (List.range (nVariants 2 .B)).all (fun i => (unreported 2 .B).contains i || sound 2 .B i) = true := by
  decide +kernel
example : unreported 2 .B = [6, 7, 8, 42, 43, 44, 45, 46, 47, 48, 49, 58, 59, 60, 61, 62, 63, 64, 65] := by decide +kernel
example : (List.range (nVariants 2 .I)).all (fun i => (unreported 2 .I).contains i || sound 2 .I i) = true := by
  decide +kernel
example : unreported 2 .I = [0, 10, 43, 46, 59, 62] := by decide +kernel
example : (List.range (nVariants 2 .J)).all (fun i => (unreported 2 .J).contains i || sound 2 .J i) = true := by
  decide +kernel
example : unreported 2 .J = [0, 43, 46, 59, 62, 88] := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 44 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 45 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 47 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 49 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 58 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 60 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 61 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 63 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 64 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .A 65 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 44 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 45 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 47 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 49 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 58 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 60 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 61 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 63 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 64 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 65 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .B 75 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .I 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .I 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .I 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .I 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .I 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .I 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 13 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 26 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 29 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 1 .J 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 44 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 45 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 47 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 49 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 58 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 60 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 61 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 63 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 64 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .A 65 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 42 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 44 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 45 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 47 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 49 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 58 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 60 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 61 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 63 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 64 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .B 65 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .I 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .I 10 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .I 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .I 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .I 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .I 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .J 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .J 43 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .J 46 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .J 59 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .J 62 = true := by decide +kernel
set_option maxHeartbeats 0 in
example : sound 2 .J 88 = true := by decide +kernel

end BinCompat

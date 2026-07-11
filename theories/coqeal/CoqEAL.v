(*
  Copyright (C) 2026 Ilya I. Nikitin <ilya.i.nikitin@proton.me>
  SPDX-License-Identifier: GPL-3.0-or-later

  CoqEAL notation dictionary for rendering Rocq -> Typst. It covers the
  refinement relation, the operations of the Op layer, which are class
  projections, and the matrix operations of the seqmx representation.
*)

From elpi Require Import elpi.
From CoqEAL Require Import refinements seqmx.
From Typst Require Import Core Mathcomp.

Elpi Accumulate typst.db lp:{{

% CoqEAL: refined programs and their operations
% the refinement relation  refines R x y  ->  x ~ y
:before "pp-app.fallback"
pp-app Ctx GR [_, _, _, X, Y] S :- gsuf "refinements.refines" GR, !,
  pp-rel Ctx " tilde.op " X Y S.

% product of matrices on the operations layer
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "seqmx.hmul_op" GR,
  but-last Args R0, std.last Args B, std.last R0 A, !,
  pp 30 A SA, pp 31 B SB, RAW is SA ^ " " ^ SB, paren Ctx 30 RAW S.

% scalar operations, which are class projections, with the operands last
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "Op.mul_op" GR,
  but-last Args R0, std.last Args B, std.last R0 A,
  head B IG IArgs, gsuf "Op.inv_op" IG, std.last IArgs Y, !,
  pp 30 A SA, pp 31 Y SY, RAW is SA ^ " / " ^ SY, paren Ctx 30 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "Op.mul_op" GR,
  but-last Args R0, std.last Args B, std.last R0 A, !,
  pp 30 A SA, pp 31 B SB, RAW is SA ^ " " ^ SB, paren Ctx 30 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "Op.add_op" GR,
  but-last Args R0, std.last Args B, std.last R0 A, !,
  pp-bin Ctx 20 " + " A B S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "Op.sub_op" GR,
  but-last Args R0, std.last Args B, std.last R0 A, !,
  pp-bin Ctx 20 " - " A B S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "Op.opp_op" GR, std.last Args X, !,
  pp 30 X SX, RAW is "- " ^ SX, paren Ctx 25 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "Op.inv_op" GR, std.last Args X, !,
  pp 41 X SX, RAW is SX ^ "^(-1)", paren Ctx 40 RAW S.
:before "pp-app.fallback"
pp-app _ GR _ "0" :- gsuf "Op.zero_op" GR, !.
:before "pp-app.fallback"
pp-app _ GR _ "1" :- gsuf "Op.one_op" GR, !.

% scalar matrix and trace on the operations layer
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "scalar_seqmx" GR, std.last Args X,
  is-ring-one X, !, but-last Args R0, std.last R0 N,
  rank-str N RN, style-fmt "identity" [RN] S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "scalar_seqmx" GR, std.last Args X, !,
  but-last Args R0, std.last R0 N, rank-str N RN,
  pp 41 X SX, style-fmt "identity" [RN] SI,
  RAW is SX ^ " " ^ SI, paren Ctx 30 RAW S.
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "trace_seqmx" GR, std.last Args X, !,
  pp 0 X SX, style-fmt "op-trace" [SX] S.

}}.

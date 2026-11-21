(*
  Copyright (C) 2026 Ilya I. Nikitin <ilya.i.nikitin@proton.me>
  SPDX-License-Identifier: GPL-3.0-or-later

  infotheo notation dictionary for rendering Rocq -> Typst: the probability
  function of a finite distribution.
*)

From elpi Require Import elpi.
From infotheo.probability Require Import fdist.
From Typst Require Import Core.

Elpi Accumulate typst.db lp:{{

% the probability function of a distribution: the projection itself is
% transparent to printing
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "FDist.f" GR, std.last Args Mu,
  coq.typecheck Mu TyMu ok, head-suf "FDist.t" TyMu, !, pp Ctx Mu S.
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "FDist.f" GR,
  but-last Args R0, std.last Args X, std.last R0 Mu, !,
  pp 50 Mu SMu, pp 0 X SX, app-paren SMu SX S.

}}.

(*
  Copyright (C) 2026 Ilya I. Nikitin <ilya.i.nikitin@proton.me>
  SPDX-License-Identifier: GPL-3.0-or-later

  Notation dictionary of mathcomp-analysis and mathcomp-classical for
  rendering Rocq -> Typst. It covers limits and convergence, where the filters
  are stripped, continuity, the choice operators pselect and cid, Hermitian
  matrices and the real qualifier.
*)

From elpi Require Import elpi.
From mathcomp Require Import boolp topology.
From Typst Require Import Core Mathcomp.

Elpi Accumulate typst.db lp:{{

% the condition of the choice operator on decidability  pselect P  ->  P
select-arg Sc A :- head Sc G [A], gsuf "boolp.pselect" G.

% choice operators without construction, where the witness has no explicit form
is-choice G :- gsuf "indefinite_description" G.
is-choice G :- gsuf "boolp.cid" G.

% the sequence under a limit: strip the neighbourhood and the filter image  u @ \oo
pred limit-seq i:term, o:string.
limit-seq T S :- head T G A, gsuf "filter.nbhs" G, std.last A Inner, !,
  limit-seq Inner S.
limit-seq T S :- head T G A, gsuf "filter.fmap" G, !,
  but-last A Rest, std.last Rest Seq, seq-render Seq S.
limit-seq T S :- seq-render T S.

% a partially applied sequence, for example A ^+ : nat -> 'M_n, is printed
% through eta-expansion over a fresh index k
pred seq-render i:term, o:string.
seq-render T S :- pp 2 T S0, not (S0 = "?"), !, S = S0.
seq-render T S :- coq.typecheck T Ty ok, Ty = prod _ Dom _, is-nat-type Dom, !,
  @pi-decl `k` Dom x\ (name-of x "k" :- !) =>
    (sigma TX\ coq.mk-app T [x] TX, pp 2 TX S).
seq-render _ "?".

% the limit: strip the neighbourhood  nbhs l
pred limit-lim i:term, o:string.
limit-lim T S :- head T G A, gsuf "filter.nbhs" G, !, std.last A L, pp 2 L S.
limit-lim T S :- pp 2 T S.


% analysis: limits
% convergence  u @ \oo --> l  ->  u --> l , image filter and neighbourhood stripped
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "topology_structure.cvg_to" GR, !,
  limit-seq A SA, limit-lim B SB, RAW is SA ^ " --> " ^ SB, paren Ctx 1 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "cvg_to" GR, !,
  limit-seq A SA, limit-lim B SB, RAW is SA ^ " --> " ^ SB, paren Ctx 1 RAW S.

% the convergence predicate  cvgn u  ->  exists L, u --> L
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "topology_structure.cvgn" GR, std.last Args U, !,
  limit-seq U SU, q "L" QL,
  RAW is "exists " ^ QL ^ ", " ^ SU ^ " --> " ^ QL, paren Ctx 0 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "lim_sup.cvgn" GR, std.last Args U, !,
  limit-seq U SU, q "L" QL,
  RAW is "exists " ^ QL ^ ", " ^ SU ^ " --> " ^ QL, paren Ctx 0 RAW S.

% continuity at a point  continuous_at x f
:before "pp-app.fallback"
pp-app Ctx GR [_, _, X, F] S :- gsuf "continuous_at" GR, !,
  pp 41 F SF, pp 0 X SX,
  RAW is SF ^ " \"непр. в\" " ^ SX, paren Ctx 10 RAW S.

% continuity as a named predicate
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "continuous" GR, std.last Args F, !,
  pp 50 F SF, S is "op(\"непр.\")(" ^ SF ^ ")".


% qualifiers
:before "render-qual.fallback"
render-qual Q S :- head Q G _, gsuf "Def.real_num" G, !,
  style-fmt "set-real" [] S.
:before "render-qual.fallback"
render-qual Q S :- head Q G [F, N, _, _], gsuf "sesquilinear.hermitianmx" G, !,
  pp 0 N SN, carrier-name F SC, style-fmt "qual-herm" [SN, SC] S.

}}.

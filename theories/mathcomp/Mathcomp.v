(*
  Copyright (C) 2026 Ilya I. Nikitin <ilya.i.nikitin@proton.me>
  SPDX-License-Identifier: GPL-3.0-or-later

  Mathematical Components notation dictionary for rendering Rocq -> Typst.

  The clauses extend the open predicates of the typst.db database, see
  Typst.Core. They provide the pp-app dictionary for the operations of ssrnat,
  ssralg, ssrnum, order, poly, matrix and bigop, helpers for type domains such
  as matrices, ordinals and carriers of structures, membership qualifiers, and
  the decomposition of matrix sums and products for line-by-line layout.
*)

From elpi Require Import elpi.
From mathcomp Require Import ssreflect ssralg matrix.
From Typst Require Import Core.

Elpi Accumulate typst.db lp:{{

% helpers
pred is-ring-one i:term.                        % ring one  1
is-ring-one T :- head T G _, gsuf "GRing.one" G.

pred is-natmul i:gref.                           % multiple of one  *+ / %:R
is-natmul G :- gsuf "Algebra.natmul" G.
is-natmul G :- gsuf "GRing.natmul" G.

pred is-norm i:gref.                              % norm or absolute value  |.|
is-norm G :- gsuf "Num.norm" G.
is-norm G :- gsuf "POrderedZmodule.norm" G.
is-norm G :- gsuf "normedZmodType.norm" G.

is-field-type T :- head-suf "ClosedField.type" T.
is-field-type T :- head-suf "NumField.type" T.
is-field-type T :- head-suf "ComUnitRing.type" T.

index-type T :- head-suf "fintype.ordinal" T.
index-type T :- head-suf "Finite.sort" T.

% the inner factor of an adjoint  X† = map_mx conj (trmx X)  ->  X
adjoint-arg T X :- head T GR [_, _, CONJ, _, _, INNER],
  gsuf "matrix.map_mx" GR, head CONJ CG _, gsuf "Num.conj" CG,
  head INNER IG TArgs, gsuf "matrix.trmx" IG, std.last TArgs X.

% the name of a carrier: strip the sort projections and the structure
% coercions down to a named variable
pred carrier-name i:term, o:string.
carrier-name T S :- name-of T Nm, !, q Nm S.
carrier-name T S :- head T _ Args, std.last Args X, carrier-name X S.

% a compound dimension or size is wrapped in parentheses
pred dim-atom i:string, o:string.
dim-atom D D :- rex.match "^[^ ,]+$" D, !.
dim-atom D S :- S is "(" ^ D ^ ")".

% the size of the identity matrix, the slot of style "identity"
pred rank-str i:term, o:string.
rank-str N S :- pp 0 N S0, dim-atom S0 S.

% the qualifier of a predicate from  mem (has_quality O _ qual) | mem qual
qualifier-of MemE QStr :-
  head MemE MG MArgs, gsuf "ssrbool.mem" MG,
  std.last MArgs HQ,
  ( head HQ HG HArgs, gsuf "ssrbool.has_quality" HG, !, std.last HArgs Qual
  ; Qual = HQ ),
  render-qual Qual QStr.

% the parameters of the class of upper triangular matrices, taken from an
% application of is_trig_mx: the ring, the sizes and the matrix
pred trig-qual i:list term, o:string.
trig-qual [R | Rest] QT :- but-last [R | Rest] R0, std.last R0 N,
  pp 0 N SN, carrier-name R SC, style-fmt "qual-trig" [SN, SC] QT.

:before "render-qual.fallback"
render-qual Q S :- head Q G [F | Rest], gsuf "spectral.unitarymx" G,
  std.last [F | Rest] N, !,
  pp 0 N SN, carrier-name F SC, style-fmt "qual-unitary" [SN, SC] S.
:before "render-qual.fallback"
render-qual Q S :- head Q G [F, N], gsuf "matrix.unitmx" G, !,
  pp 0 N SN, carrier-name F SC, style-fmt "qual-gl" [SN, SC] S.

% a diagonal entry:  fun i j => match (i == j) [diag; off]
pred diag-entry i:term, o:string, o:string.
diag-entry (fun Ni Ti Fi) DL OL :-
  @pi-decl Ni Ti i\ diag-entry (Fi i) DL OL.
diag-entry (match Scrut _ [TB, FB]) DL OL :-
  head Scrut SG _, gsuf "eqtype.eq_op" SG, !,
  ( TB = app [L | _], name-of L DL ; pp 50 TB DL ), !,
  pp 50 FB OL.

% a general matrix:  fun i j => E  ->  (E)_(i,j)
pred general-mat i:term, o:string.
general-mat (fun Ni Ti Fi) S :-
  coq.name->id Ni I,
  @pi-decl Ni Ti i\ (name-of i I :- !) => general-mat-2 I (Fi i) S.
pred general-mat-2 i:string, i:term, o:string.
general-mat-2 I (fun Nj Tj Fj) S :-
  coq.name->id Nj J, q I QI, q J QJ,
  @pi-decl Nj Tj j\ (name-of j J :- !) =>
    ( pp 0 (Fj j) E, S is "(" ^ E ^ ")_(" ^ QI ^ "," ^ QJ ^ ")" ).

% a summand of a sum:  fun i => BigBody ... val  ->  the index with its bound
% together with the value. The bound of an ordinal index is taken from its
% type  'I_k. A clash between the name of the index and the name of the bound
% is resolved by a prime
pred big-summand i:term, o:string, o:string.
big-summand (fun N T Fi) IdxS VS :- !,
  coq.name->id N I0,
  ( head T TG KArgs, gsuf "fintype.ordinal" TG, std.last KArgs K,
    pp 0 K SK,
    ( q I0 SK, I is I0 ^ "'" ; I = I0 ), !,
    q I QI, IdxS is QI ^ " < " ^ SK
  ; I = I0, q I QI, IdxS = QI ),
  @pi-decl N T x\ (name-of x I :- !) => big-val (Fi x) VS.
big-summand B "`i`" VS :- pp 50 B VS.

pred big-val i:term, o:string.
big-val Body VS :- head Body G AllArgs, gsuf "bigop.BigBody" G, !,
  std.last AllArgs V, pp 21 V VS.
big-val Body VS :- pp 21 Body VS.

% matrices are object candidates for repeat extraction
cse-obj-type T :- head T GTy _, gsuf "matrix.matrix" GTy.

% the range of a binder taken from its type, as a postfix to the name:
% a matrix gives in C^(m times n) and a vector gives in C^n,
% an ordinal gives < n, and a carrier of a structure gives in C
type-domain T S :- head T GR [C, M, N], gsuf "matrix.matrix" GR, !,
  carrier-name C SC,
  ( is-one N, not (is-one M), !, pp 0 M SM0, dim-atom SM0 SM,
    style-fmt "space-col" [SC, SM] S0
  ; is-one M, not (is-one N), !, pp 0 N SN0, dim-atom SN0 SN,
    style-fmt "space-row" [SC, SN] S0
  ; is-one M, is-one N, !, S0 = SC
  ; pp 0 M SM0, pp 0 N SN0, dim-atom SM0 SM, dim-atom SN0 SN,
    style-fmt "space-mx" [SC, SM, SN] S0 ),
  S is "in " ^ S0.
type-domain T S :- head T GR Args, gsuf "fintype.ordinal" GR,
  std.last Args K, !, pp 0 K SK, style-fmt "bound-ord" [SK] S.
type-domain T S :- head T GR _, gsuf ".sort" GR, !,
  carrier-name T SC, S is "in " ^ SC.

% constraints on a variable that can be folded in
var-constraint1 T Nm C :- head T GR [_, Elt, MemE], gsuf "ssrbool.in_mem" GR,
  name-of Elt Nm, qualifier-of MemE QStr, !, C is "in " ^ QStr.
var-constraint1 T Nm C :- head T GR Args, gsuf "is_trig_mx" GR,
  std.last Args X, name-of X Nm, !,
  trig-qual Args QT, C is "in " ^ QT.

% crossed relations
neg-rel Ctx T S :- head T GR [_, A, B], gsuf "eqtype.eq_op" GR, !,
  pp-rel Ctx " eq.not " A B S.
neg-rel Ctx T S :- head T GR [_, _, A, B], gsuf "Order.le" GR, !,
  pp-rel Ctx " lt.eq.not " A B S.
neg-rel Ctx T S :- head T GR [_, _, A, B], gsuf "Order.lt" GR, !,
  pp-rel Ctx " lt.not " A B S.
neg-rel Ctx T S :- head T GR [A, B], gsuf "ssrnat.leq" GR, !,
  pp-rel Ctx " lt.eq.not " A B S.
neg-rel Ctx T S :- head T GR [_, Elt, MemE], gsuf "ssrbool.in_mem" GR,
  qualifier-of MemE QStr, !,
  pp 11 Elt SE, RAW is SE ^ " in.not " ^ QStr, paren Ctx 10 RAW S.
neg-rel Ctx T S :- head T GR Args, gsuf "is_trig_mx" GR, std.last Args M, !,
  pp 11 M SM, trig-qual Args QT,
  RAW is SM ^ " in.not " ^ QT, paren Ctx 10 RAW S.

% the main relations of statements
rel-sides T "=" A B :- head T GR [_, A, B], gsuf "eqtype.eq_op" GR, !.
rel-sides T "<=" A B :- head T GR [_, _, A, B], gsuf "Order.le" GR, !.
rel-sides T "<" A B :- head T GR [_, _, A, B], gsuf "Order.lt" GR, !.

% structure operator heads are left folded by the structural decomposition
struct-head G :- gsuf "Algebra.add" G.
struct-head G :- gsuf "Algebra.opp" G.
struct-head G :- gsuf "matrix.mulmx" G.
struct-head G :- gsuf "Order.le" G.
struct-head G :- gsuf "Order.lt" G.

% decomposition of a matrix product into factors
:before "flatten-mul.fallback"
flatten-mul T0 L :- expose T0 T,
  head T G [_, _, _, _, A, B], gsuf "matrix.mulmx" G, !,
  flatten-mul A LA, std.append LA [B] L.

% decomposition of a ring sum into summands
:before "flatten-sum.fallback"
flatten-sum T0 L :- expose T0 T,
  head T G [_, A, B], gsuf "Algebra.add" G,
  head B OG [_, Y], gsuf "Algebra.opp" OG, !,
  flatten-sum A LA, std.append LA [addend "-" Y] L.
:before "flatten-sum.fallback"
flatten-sum T0 L :- expose T0 T,
  head T G [_, A, B], gsuf "Algebra.add" G, !,
  flatten-sum A LA, std.append LA [addend "+" B] L.

% the Frobenius norm form written as the trace of a product with an adjoint
frob-inner T M :- head T GR [_, _, PROD], gsuf "matrix.mxtrace" GR,
  head PROD MG [_, _, _, _, ADJ, X], gsuf "matrix.mulmx" MG,
  adjoint-arg ADJ X, !, M = X.


% pp-app dictionary
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "eqtype.eq_op" GR, !, pp-rel Ctx " = " A B S.

% natural numbers
:before "pp-app.fallback"
pp-app Ctx GR [A, B] S :- gsuf "ssrnat.leq" GR, !, pp-rel Ctx " <= " A B S.
:before "pp-app.fallback"
pp-app Ctx GR [A, B] S :- gsuf "ssrnat.subn" GR, !, pp-bin Ctx 20 " - " A B S.
:before "pp-app.fallback"
pp-app Ctx GR [A, B] S :- gsuf "ssrnat.addn" GR, !, pp-bin Ctx 20 " + " A B S.
:before "pp-app.fallback"
pp-app Ctx GR [A, B] S :- gsuf "ssrnat.muln" GR, !, pp-bin Ctx 30 " " A B S.
:before "pp-app.fallback"
pp-app _ GR [A, B] S :- gsuf "ssrnat.maxn" GR, !,
  pp 0 A SA, pp 0 B SB, S is "max(" ^ SA ^ ", " ^ SB ^ ")".
:before "pp-app.fallback"
pp-app _ GR [A, B] S :- gsuf "ssrnat.minn" GR, !,
  pp 0 A SA, pp 0 B SB, S is "min(" ^ SA ^ ", " ^ SB ^ ")".


% ring and order
:before "pp-app.fallback"
pp-app _ GR _ "0" :- gsuf "Algebra.zero" GR, !.
:before "pp-app.fallback"
pp-app _ GR _ "0" :- gsuf "GRing.zero" GR, !.
:before "pp-app.fallback"
pp-app _ GR _ "1" :- gsuf "GRing.one" GR, !.

% subtraction  a + (- b)  ->  a - b
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "Algebra.add" GR,
  head B OG [_, Y], gsuf "Algebra.opp" OG, !, pp-bin Ctx 20 " - " A Y S.
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "Algebra.add" GR, !, pp-bin Ctx 20 " + " A B S.
:before "pp-app.fallback"
pp-app Ctx GR [_, A] S :- gsuf "Algebra.opp" GR, !,
  pp 30 A SA, RAW is "- " ^ SA, paren Ctx 25 RAW S.

% quotient  x y^(-1)  ->  the fraction x / y
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "GRing.mul" GR,
  head B IG [_, Y], gsuf "GRing.inv" IG, !,
  pp 30 A SA, pp 31 Y SY, RAW is SA ^ " / " ^ SY, paren Ctx 30 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR [_, A, B] S :- gsuf "GRing.mul" GR, !, pp-bin Ctx 30 " " A B S.

% a multiple of one  n%:R -> n , otherwise  x *+ n -> n x
:before "pp-app.fallback"
pp-app _ GR [_, X, N] S :- is-natmul GR, is-ring-one X, !, pp 50 N S.
:before "pp-app.fallback"
pp-app Ctx GR [_, X, N] S :- is-natmul GR, !,
  pp 50 N SN, pp 41 X SX, RAW is SN ^ " " ^ SX, paren Ctx 30 RAW S.

% absolute value  |x| , the operand being the last argument
:before "pp-app.fallback"
pp-app _ GR Args S :- is-norm GR, std.last Args X, !,
  pp 0 X SX, S is "abs(" ^ SX ^ ")".

% scaling  a *: x  ->  a x , the last two arguments being the scalar and the vector
:before "pp-app.fallback"
pp-app Ctx GR Args S :- ( gsuf "GRing.scale" GR ; gsuf "matrix.scalemx" GR ),
  but-last Args R0, std.last Args X, std.last R0 A, !,
  pp 41 A SA, pp 31 X SX, RAW is SA ^ " " ^ SX, paren Ctx 30 RAW S.

% applying a morphism  r2c x -> r2c(x) , a partial application stays the morphism
:before "pp-app.fallback"
pp-app _ GR [_, _, F, X] S :- gsuf "RMorphism.sort" GR, !,
  pp 50 F SF, pp 0 X SX, app-paren SF SX S.
:before "pp-app.fallback"
pp-app Ctx GR [_, _, F] S :- gsuf "RMorphism.sort" GR, !, pp Ctx F S.

% inverse element  x^-1  ->  x^(-1)
:before "pp-app.fallback"
pp-app Ctx GR [_, X] S :- gsuf "GRing.inv" GR, !,
  pp 41 X SX, RAW is SX ^ "^(-1)", paren Ctx 40 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR [_, X, N] S :- gsuf "GRing.exp" GR, !,
  pp 41 X SX, pp 50 N SN, RAW is SX ^ "^(" ^ SN ^ ")", paren Ctx 40 RAW S.
:before "pp-app.fallback"
pp-app Ctx GR [_, _, A, B] S :- gsuf "Order.le" GR, !, pp-rel Ctx " <= " A B S.
:before "pp-app.fallback"
pp-app Ctx GR [_, _, A, B] S :- gsuf "Order.lt" GR, !, pp-rel Ctx " < " A B S.


% polynomials and determinant
% derivative of a polynomial  p^`()  ->  p'
:before "pp-app.fallback"
pp-app Ctx GR [_, P] S :- gsuf "poly.deriv" GR, !,
  pp 41 P SP, RAW is SP ^ "'", paren Ctx 40 RAW S.

% characteristic matrix  char_poly_mx A  ->  x bb(1) - A
:before "pp-app.fallback"
pp-app Ctx GR [_, N, A] S :- gsuf "char_poly_mx" GR, !,
  pp 21 A SA, rank-str N RN, style-fmt "identity" [RN] SI,
  RAW is "x " ^ SI ^ " - " ^ SA, paren Ctx 20 RAW S.

% characteristic polynomial  char_poly A  ->  chi_A
:before "pp-app.fallback"
pp-app _ GR [_, _, A] S :- gsuf "char_poly" GR, !,
  pp 50 A SA, subscript "chi" SA S.

% determinant and adjugate matrix
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "matrix.determinant" GR, std.last Args A, !,
  pp 0 A SA, style-fmt "op-det" [SA] S.
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "matrix.adjugate" GR, std.last Args A, !,
  pp 0 A SA, style-fmt "op-adj" [SA] S.

% embedding of constants  c%:P -> c  and the polynomial variable  'X -> x
:before "pp-app.fallback"
pp-app Ctx GR [_, C] S :- gsuf "poly.polyC" GR, !, pp Ctx C S.
:before "pp-app.fallback"
pp-app _ GR [_] "x" :- gsuf "poly.polyX" GR, !.

% value of a polynomial  p.[a]  ->  p(a)
:before "pp-app.fallback"
pp-app _ GR [_, P, A] S :- gsuf "poly.horner" GR, !,
  pp 50 P SP, pp 0 A SA, app-paren SP SA S.

% iteration of a function  iter n f x  ->  f^(∘ n)(x)
:before "pp-app.fallback"
pp-app Ctx GR [_, N, F, X] S :- gsuf "ssrnat.iter" GR, !,
  pp 50 F SF, pp 41 N SN, pp 0 X SX,
  style-fmt "iterate" [SF, SN, SX] RAW, paren Ctx 40 RAW S.

% value of a finite function through the finfun coercion  f x  ->  f(x)
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "fun_of_fin" GR,
  but-last Args R0, std.last Args X, std.last R0 F, !,
  pp 50 F SF, pp 0 X SX, app-paren SF SX S.


% matrices
% identity and scalar matrix  scalar_mx a  ->  E_n or a E_n , see style "identity"
:before "pp-app.fallback"
pp-app _ GR [_, N, A] S :- gsuf "matrix.scalar_mx" GR, is-ring-one A, !,
  rank-str N RN, style-fmt "identity" [RN] S.
:before "pp-app.fallback"
pp-app Ctx GR [_, N, A] S :- gsuf "matrix.scalar_mx" GR, !,
  pp 41 A SA, rank-str N RN, style-fmt "identity" [RN] SI,
  RAW is SA ^ " " ^ SI, paren Ctx 30 RAW S.

% product of matrices  A B , left-associative
:before "pp-app.fallback"
pp-app Ctx GR [_, _, _, _, A, B] S :- gsuf "matrix.mulmx" GR, !,
  pp 30 A SA, pp 31 B SB, RAW is SA ^ " " ^ SB, paren Ctx 30 RAW S.

% inverse matrix  invmx M  ->  M^(-1)
:before "pp-app.fallback"
pp-app Ctx GR [_, _, M] S :- gsuf "matrix.invmx" GR, !,
  pp 41 M SM, RAW is SM ^ "^(-1)", paren Ctx 40 RAW S.

% conjugate transpose  map_mx conj (trmx X)  ->  X^*
:before "pp-app.fallback"
pp-app Ctx GR [_, _, CONJ, _, _, INNER] S :-
  gsuf "matrix.map_mx" GR, head CONJ CG _, gsuf "Num.conj" CG,
  head INNER IG TArgs, gsuf "matrix.trmx" IG, !,
  std.last TArgs X, pp 41 X SX, style-fmt "adjoint" [] AJ,
  RAW is SX ^ AJ, paren Ctx 40 RAW S.

% entrywise conjugation  map_mx conj X  ->  overline(X)
:before "pp-app.fallback"
pp-app Ctx GR [_, _, CONJ, _, _, X] S :-
  gsuf "matrix.map_mx" GR, head CONJ CG _, gsuf "Num.conj" CG, !,
  pp 0 X SX, style-fmt "conjugate" [SX] RAW, paren Ctx 40 RAW S.

% entrywise application of a function  map_mx f X  ->  f(X)
:before "pp-app.fallback"
pp-app _ GR [_, _, F, _, _, X] S :- gsuf "matrix.map_mx" GR, !,
  pp 50 F SF, pp 0 X SX, app-paren SF SX S.

% transposition  trmx X  ->  X^T
:before "pp-app.fallback"
pp-app Ctx GR TArgs S :- gsuf "matrix.trmx" GR, !,
  std.last TArgs X, pp 41 X SX, style-fmt "transpose" [] TR,
  RAW is SX ^ TR, paren Ctx 40 RAW S.

% the trace of a 1x1 matrix is a scalar, a quadratic form, otherwise tr(X)
:before "pp-app.fallback"
pp-app Ctx GR [_, Dim, X] S :- gsuf "matrix.mxtrace" GR, is-one Dim, !,
  pp Ctx X S.

% trace of a product with an adjoint  tr (X† X)  ->  norm(X)_F^2 ,
% the Frobenius norm form written without a named definition
:before "pp-app.fallback"
pp-app Ctx GR [_, _, PROD] S :- gsuf "matrix.mxtrace" GR,
  head PROD MG [_, _, _, _, ADJ, X], gsuf "matrix.mulmx" MG,
  adjoint-arg ADJ X, !,
  pp 0 X SX, style-fmt "frob-sq" [SX] RAW, paren Ctx 40 RAW S.
:before "pp-app.fallback"
pp-app _ GR [_, _, X] S :- gsuf "matrix.mxtrace" GR, !,
  pp 0 X SX, style-fmt "op-trace" [SX] S.

% coordinate of the i-th column: the ordinal -> nat coercion is dropped
:before "pp-app.fallback"
pp-app Ctx GR [_, I] S :- gsuf "fintype.nat_of_ord" GR, !, pp Ctx I S.

% matrix entry  M i j  ->  M_(i,j)
:before "pp-app.fallback"
pp-app Ctx GR [_, _, _, M, I, J] S :- gsuf "matrix.fun_of_matrix" GR, !,
  pp 50 M SM, pp 0 I SI, pp 0 J SJ, IJ is SI ^ "," ^ SJ,
  subscript SM IJ RAW, paren Ctx 50 RAW S.

% diagonal matrix  \matrix_(i,j) (if i==j then f i else 0)
:before "pp-app.fallback"
pp-app _ GR [_, _, _, _, EntryFun] S :- gsuf "matrix_of_fun.body" GR,
  diag-entry EntryFun DL OL, !,
  S is "mat("
    ^ DL ^ "_1, " ^ OL ^ ", dots.h, " ^ OL ^ "; "
    ^ OL ^ ", " ^ DL ^ "_2, dots.h, " ^ OL ^ "; "
    ^ "dots.v, dots.v, dots.down, dots.v; "
    ^ OL ^ ", " ^ OL ^ ", dots.h, " ^ DL ^ "_n)".

% general matrix constructor  \matrix_(i,j) E  ->  (E)_(i,j)
:before "pp-app.fallback"
pp-app _ GR [_, _, _, _, EntryFun] S :- gsuf "matrix_of_fun.body" GR, !,
  general-mat EntryFun S.

% sum over a finite type  \big[+/0]_(i < k) F i  ->  sum_(i < k) (F)
:before "pp-app.fallback"
pp-app _ GR Args S :- gsuf "bigop.bigop.body" GR, !,
  std.last Args BodyFun, big-summand BodyFun IdxS V,
  S is "sum_(" ^ IdxS ^ ") (" ^ V ^ ")".

% upper triangular matrix  is_trig_mx T  ->  T in "ВТ"
:before "pp-app.fallback"
pp-app Ctx GR Args S :- gsuf "is_trig_mx" GR, std.last Args T, !,
  pp 11 T ST, trig-qual Args QT,
  RAW is ST ^ " in " ^ QT, paren Ctx 10 RAW S.


% membership  x \is qual  ->  x in <qual>
:before "pp-app.fallback"
pp-app Ctx GR [_, Elt, MemE] S :- gsuf "ssrbool.in_mem" GR,
  qualifier-of MemE QStr, !,
  pp 11 Elt SE, RAW is SE ^ " in " ^ QStr, paren Ctx 10 RAW S.

}}.

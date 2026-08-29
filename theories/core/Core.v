(*
  Copyright (C) 2026 Ilya I. Nikitin <ilya.i.nikitin@proton.me>
  SPDX-License-Identifier: GPL-3.0-or-later

  Rendering of Rocq statements into Typst math markup through coq-elpi.

  The core walks terms, handles quantifiers and precedences, unfolds unknown
  definitions, factors out repeated subterms and emits JSON. The notation
  dictionary is open. The typst.db database declares the extension points
  pp-app, style, const-notation, target, render-qual, qualifier-of,
  type-domain and others. Dictionary packages for mathcomp, analysis, CoqEAL
  and infotheo, together with the consumer project, add their own clauses to
  them. Named anchors such as :name "pp-app.fallback" ensure that specific
  clauses are tried before generic ones regardless of package load order.

  This file also declares the RenderTypst command. It prints the statements
  listed by the target clauses and writes JSON to the path taken from the
  command's first argument, or from the ROCQ2TYPST_OUT environment variable
  when that argument is absent.
*)

From elpi Require Import elpi.

Elpi Db typst.db lp:{{

% string helpers
pred ends_with i:string, i:string.            % ends_with Full Suf
ends_with Full Suf :-
  S is size Full, P is size Suf, P =< S, Start is S - P,
  Suf is substring Full Start P.

pred gsuf i:string, i:gref.                    % name of GR ends with Suf
gsuf Suf GR :- coq.gref->string GR Full, ends_with Full Suf.

% Rocq identifiers are wrapped in backticks where they are produced. A single
% post-step format-idents, invoked from render-one, turns them into markup
% without touching the expression structure or the operator names op("...").
pred q i:string, o:string.                      % mark a name as an identifier
q R S :- S is "`" ^ R ^ "`".
pred vname i:name, o:string.                    % binder name -> tagged
vname N S :- coq.name->id N R, q R S.

% Post-step: `_` introduces a subscript, a multi-letter name becomes literal
% text. A single Latin letter, possibly with digits or primes, as well as
% symbols and unicode such as ω and ℂ, is kept as is. A name containing `_`
% is split into a base and a subscript.
% Segments between backticks alternate: structure, identifier, structure and
% so on. The leading space guarantees that rex.split does not drop the empty
% first segment, so identifiers land on odd positions.
pred format-idents i:string, o:string.
format-idents In Out :- In2 is " " ^ In, rex.split "`" In2 Parts,
  fmt-parts 0 Parts Out0, std.string.concat "" Out0 Out1,
  L is size Out1 - 1, Out is substring Out1 1 L.
pred fmt-parts i:int, i:list string, o:list string.
fmt-parts _ [] [] :- !.
fmt-parts I [P | Ps] [Q | Qs] :-
  ( 1 is I mod 2, sanitize P Q, ! ; Q = P ),
  I1 is I + 1, fmt-parts I1 Ps Qs.

pred sanitize i:string, o:string.
sanitize Raw Out :-
  rex.split "_" Raw Parts,
  ( Parts = [One], !, sanitize-atom One Out
  ; Parts = [Base | Subs], sanitize-atom Base BS,
    std.map Subs sanitize-atom SubS, std.string.concat " " SubS Sub,
    subscript BS Sub Out ).

% Subscript without redundant parentheses: a simple one, carrying no spaces
% or commas, gives `x_i`, a compound one gives `x_(i + 1)`.
pred subscript i:string, i:string, o:string.
subscript Base Sub Out :- rex.match "^[^ ,]+$" Sub, !, Out is Base ^ "_" ^ Sub.
subscript Base Sub Out :- Out is Base ^ "_(" ^ Sub ^ ")".

% Common abbreviations of Greek letters map to Typst symbol names, which
% render as the corresponding letter such as λ, ε or Σ.
pred greek-name i:string, o:string.
greek-name "lam" "lambda".
greek-name "eps" "epsilon".
greek-name "sig" "sigma".
greek-name "del" "delta".
greek-name "gam" "gamma".
greek-name "Sigma" "Sigma".
greek-name "Theta" "Theta".
greek-name "Xi" "Xi".
greek-name "Psi" "Psi".
greek-name "Pi" "Pi".
greek-name "Omega" "Omega".
greek-name "Gamma" "Gamma".
greek-name "Phi" "Phi".

pred sanitize-atom i:string, o:string.
sanitize-atom A G :- greek-name A G, !.
sanitize-atom A A :- rex.match "^[A-Za-z]'*$" A, !.        % letter, with primes
sanitize-atom A Out :- rex.match "^[A-Za-z][0-9]+$" A, !,  % letter + digits -> subscript
  First is substring A 0 1, RL is size A - 1, Rest is substring A 1 RL,
  subscript First Rest Out.
sanitize-atom A A :- rex.match "^[^A-Za-z]+$" A, !.        % symbols, unicode, digits
sanitize-atom A Out :- Out is "\"" ^ A ^ "\"".            % multi-letter


% configurable notation
% Deliberate choices about the shape of the markup, among them the identity
% matrix, the expectation sign and the spaces of vectors and matrices, are
% collected in the style table: a key maps to a format whose substitution
% slots are marked with {}. Printing consults the table through style-fmt, so
% changing a notation requires no edit to the printing code. A consumer adds
% a clause with the same key and the attribute :before "style.default", and
% the first match wins.
pred style i:string, o:string.
:name "style.default"
style "identity"       "bb(1)".            % identity matrix, {} is the size
style "expectation"    "EE[{}]".           % expectation
style "space-col"      "{}^{}".            % space of column vectors
style "space-row"      "{}^{}".            % space of row vectors
style "space-mx"       "{}^({} times {})". % space of matrices
style "set-nat"        "NN".               % the naturals
style "set-real"       "RR".               % reals (\is real)
style "bound-ord"      "< {}".             % ordinal range
style "qual-herm"      "op(\"Herm\")({}, {})".    % Hermitian matrices
style "qual-unitary"   "op(\"Unitary\")({}, {})". % unitary matrices
style "qual-trig"      "op(\"ВТ\")({}, {})".      % upper triangular matrices
style "qual-gl"        "op(\"GL\")({}, {})".      % invertible matrices
style "psd"            "succ.eq 0".        % positive semidefiniteness
style "pd"             "succ 0".           % positive definiteness
style "psd-not"        "succ.eq.not 0".
style "pd-not"         "succ.not 0".
style "loewner-le"     " prec.eq ".        % Loewner order
style "loewner-le-not" " prec.eq.not ".
style "transpose"      "^T".
style "adjoint"        "^*".
style "conjugate"      "overline({})".
style "op-trace"       "op(\"tr\")({})".
style "op-det"         "op(\"det\")({})".
style "op-adj"         "op(\"adj\")({})".
style "op-diag"        "op(\"diag\")".
style "frob-sq"        "norm({})_\"F\"^2".      % squared Frobenius norm
style "iterate"        "{}^(compose {})({})".  % {f} {n} {x}
style "limit"          "lim_({} -> oo) {}".    % {index} {body}
style "cse-names"      "Sigma Theta Xi Psi".   % labels for repeats
style "cse-where"      "\"где\"".               % caption word for repeats

% maximum length of a markup line: longer statements are broken line by line
% with alignment. Overridden by a clause with the attribute
% :before "layout.default"
pred layout-width o:int.
:name "layout.default"
layout-width 110.

% Whether to break a long Frobenius norm argument along its inner sum:
% norm(A - B)_F^2 moves the summand B onto a separate line inside the norm
% brackets. Enabled by default. Overridden by a clause with the attribute
% :before "frob-break.default".
pred frob-break-inside o:bool.
:name "frob-break.default"
frob-break-inside tt.

% Whether to break a long adjoint interior along its sum:
% (A + B + C)^* moves the summands onto separate lines inside the brackets.
% Disabled by default: the adjoint is printed on a single line, and repeat
% extraction through Sigma and Theta already shortens such expressions to one
% line. Overridden by a clause with the attribute
% :before "adjoint-break.default".
pred adjoint-break-inside o:bool.
:name "adjoint-break.default"
adjoint-break-inside ff.

% substitution of arguments into a format at the {} slots. Extra arguments
% are dropped. The surrounding spaces are mandatory: rex.split drops empty
% edge segments, so a {} at the edge of a format would lose its argument.
% The braces of the pattern stay unescaped: rex.split compiles through
% Re.Str, whose parser rejects the escape \{ in ocaml-re before 1.14.0
pred style-fmt i:string, i:list string, o:string.
style-fmt Key Args Out :- style Key F, !, F1 is " " ^ F ^ " ",
  rex.split "{}" F1 [P0 | Ps],
  fmt-fill Ps Args Rest, std.string.concat "" [P0 | Rest] Out1,
  L is size Out1 - 2, Out is substring Out1 1 L.
pred fmt-fill i:list string, i:list string, o:list string.
fmt-fill [] _ [] :- !.
fmt-fill [P | Ps] [A | As] [A, P | Out] :- !, fmt-fill Ps As Out.
fmt-fill [P | Ps] [] [P | Out] :- fmt-fill Ps [] Out.


% term head decomposition
pred head i:term, o:gref, o:list term.
head (app [global GR | Args]) GR Args :- !.
head (app [pglobal GR _ | Args]) GR Args :- !.
head (global GR) GR [] :- !.
head (pglobal GR _) GR [] :- !.

pred head-suf i:string, i:term.
head-suf Suf T :- head T GR _, gsuf Suf GR.

pred is-one i:term.                             % natural number one  S O
is-one (app [global GS, global GO]) :-
  gsuf "Datatypes.S" GS, gsuf "Datatypes.O" GO.

% parameter types that are not shown in quantifiers: carriers of structures.
% The clauses are added by the mathcomp dictionary
pred is-field-type i:term.

pred is-nat-type i:term.
is-nat-type T :- T = global GR, gsuf "Datatypes.nat" GR.

pred is-prop i:term.
is-prop T :- coq.typecheck T (sort prop) ok.

% an index argument, that is a natural number, an ordinal or an element of a
% finite type. Clauses for finite types are added by the mathcomp dictionary
pred index-like i:term.
index-like A :- coq.typecheck A Ty ok, index-type Ty.
pred index-type i:term.
index-type T :- is-nat-type T.

pred unwrap-istrue i:term, o:term.              % strip the bool -> Prop coercion
unwrap-istrue T T1 :- head T G [T1], gsuf "is_true" G, !.
unwrap-istrue T T.

% A hypothesis: either a statement of sort Prop or an anonymous binder of a
% non-computational type. The CoqEAL refinement relation, for example, lives
% in Type rather than in Prop.
pred is-hyp i:name, i:term.
is-hyp _ T :- is-prop T.
is-hyp N T :- coq.name->id N "_", not (is-nat-type T), not (T = sort _),
  not (is-field-type T).


% precedence-aware printing
% Levels, where a larger number binds tighter: implication 1, iff 2, or 4,
% and 6, not 9, relations 10, plus and minus 20, unary minus 25,
% multiplication 30, power, inverse and adjoint 40, atoms 50.
pred paren i:int, i:int, i:string, o:string.   % paren Ctx Self In Out
paren Ctx Self S S :- Self >= Ctx, !.
paren _ _ S O :- O is "(" ^ S ^ ")".

% Application of a function to an argument in parentheses. The space separates
% the base, possibly carrying a subscript or a superscript, from the opening
% parenthesis: without the space the Typst parser attaches the next
% parenthesis to the index as a call, so f_i(x) reads as f_(i(x)) and M^T(x)
% as M^(T(x)). A space between an atom and a parenthesis does not affect the
% typeset width.
pred app-paren i:string, i:string, o:string.   % base, arguments
app-paren Fn Args S :- S is Fn ^ " (" ^ Args ^ ")".

pred name-of i:term, o:string.                  % names of bound variables
pred hidden-var i:term.        % hidden sample point ω under the expectation sign

% Argument of the choice operator on decidability: the clause is added by the
% mathcomp-analysis dictionary through pselect. The core only sees the
% decomposition itself.
pred select-arg i:term, o:term.

% choice operators without construction, where the witness has no explicit
% form. The clauses are added by the dictionaries
pred is-choice i:gref.

% A recursion is printed either in functional form op("name")(...) or in
% subscript form base_(...), following the const-notation table.
kind rfmode type.
type rf-call string -> rfmode.
type rf-sub string -> rfmode.
pred recfun i:term, o:rfmode.                   % marker of a recursive function

pred pp i:int, i:term, o:string.
pp _ X S :- name-of X Raw, !, q Raw S.            % bound variable
pp _ F S :- recfun F (rf-call FN), !, S is "op(\"" ^ FN ^ "\")".
pp _ F S :- recfun F (rf-sub B), !, S = B.
pp Ctx (app [F | Args]) S :- recfun F (rf-call FN), !,  % recursive call
  std.map Args (a\ r\ pp 0 a r) AS, std.string.concat ", " AS J,
  RAW is "op(\"" ^ FN ^ "\")(" ^ J ^ ")", paren Ctx 50 RAW S.
pp Ctx (app [F | Args]) S :- recfun F (rf-sub B), !,    % recurrence term
  std.filter Args (a\ not (hidden-var a)) Shown,
  ( Shown = [], !, S = B
  ; std.map Shown (a\ r\ pp 0 a r) AS, std.string.concat "," AS J,
    subscript B J RAW, paren Ctx 50 RAW S ).
pp Ctx (prod N T F) S :- is-hyp N T, !,          % implication  A => B
  pp 1 T ST, @pi-decl N T x\ pp 0 (F x) SB,
  RAW is ST ^ " => " ^ SB, paren Ctx 1 RAW S.
pp Ctx (prod N T F) S :- !,                      % chain of universal quantifiers
  pp-forall Ctx (prod N T F) [] S.

% application of a bound function: index arguments move into the subscript,
% as in l i -> l_i, the rest are printed as a functional application c2r(x)
pp Ctx (app [F | Args]) S :- name-of F Nm, !,
  q Nm QNm, std.filter Args (a\ not (hidden-var a)) Shown,
  ( Shown = [], !, S = QNm
  ; std.forall Shown index-like, !,
    std.map Shown (a\ r\ pp 0 a r) AS, std.string.concat "," AS J,
    subscript QNm J RAW, paren Ctx 50 RAW S
  ; std.map Shown (a\ r\ pp 0 a r) AS, std.string.concat ", " AS J,
    app-paren QNm J RAW, paren Ctx 50 RAW S ).
pp Ctx (app [app L | Args]) S :- !,              % flattening of a nested app
  std.append L Args L2, pp Ctx (app L2) S.
pp Ctx (app [F | Args]) S :- F = fun _ _ _, !,   % beta-redex after unfolding
  coq.mk-app F Args T2, pp Ctx T2 S.
pp Ctx (let _ _ V F) S :- !, pp Ctx (F V) S.    % a let-binding is substituted

% boolean negation  match b [false; true]  ->  crossed relation or not b
pp Ctx (match Sc _ [B1, B2]) S :-
  is-bool-false B1, is-bool-true B2, !,
  ( select-arg Sc A, !, pp-not Ctx A S
  ; pp-not Ctx Sc S ).
pp _ (match Sc _ [B1, B2]) S :-                  % identity  match b [true; false] -> b
  is-bool-true B1, is-bool-false B2, !, match-cond Sc S.
pp Ctx (match Sc _ [B1, B2]) S :- !,             % branching with two cases
  match-cond Sc Cond,
  strip-lam B1 BB1, pp 0 BB1 S1,
  strip-lam B2 BB2, pp 0 BB2 S2,
  RAW is "cases(" ^ S1 ^ " \"если\" " ^ Cond ^ ", " ^ S2 ^ " \"иначе\")",
  paren Ctx 50 RAW S.
pp _ (fix N RI Ty Recf) S :- !, fix-recurrence (fix N RI Ty Recf) S.

% choice without construction, cid and the like: the witness has no explicit form
pp _ (match Sc _ [_]) "?" :- head Sc G _, is-choice G, !.

% single-branch match: a projection of a computable constructor iota-reduces
pp Ctx (match Sc _ [Br]) S :- scrut-constructor Sc 4 CArgs,
  lam-arity Br NF, take-last NF CArgs Fields,
  coq.mk-app Br Fields Red, !, pp Ctx Red S.

% otherwise a record field is printed as an application to an argument
pp Ctx (match Sc _ [Br]) S :- !, match-record Br S0,
  ( rex.match "^`[A-Za-z_][A-Za-z0-9_']*`$" S0, pp 50 Sc SS, not (SS = "?"), !,
    app-paren S0 SS S
  ; paren Ctx 0 S0 S ).
pp Ctx (fun N T Bo) S :- !,                      % a function is printed by its body
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => pp Ctx (Bo x) S.
pp Ctx T S :- head T GR Args, pp-app Ctx GR Args S, !.
pp _ (sort _) "" :- !.
pp _ _ "?".

pred pp-bin i:int, i:int, i:string, i:term, i:term, o:string.
pp-bin Ctx Pr Op A B S :-
  PrL is Pr, PrR is Pr + 1, pp PrL A SA, pp PrR B SB,
  RAW is SA ^ Op ^ SB, paren Ctx Pr RAW S.

% relation: the operands are printed at level 11, so that a nested relation,
% for example an equality of two inequalities, gets parentheses on both sides
pred pp-rel i:int, i:string, i:term, i:term, o:string.
pp-rel Ctx Op A B S :- pp 11 A SA, pp 11 B SB,
  RAW is SA ^ Op ^ SB, paren Ctx 10 RAW S.

% a negated relation is printed with a crossed relation sign, giving
% x eq.not y instead of not x = y. Other negations use the word not
pred pp-not i:int, i:term, o:string.
pp-not Ctx T S :- unwrap-istrue T T1, neg-rel Ctx T1 S, !.
pp-not Ctx T S :- pp 41 T SA, RAW is "not " ^ SA, paren Ctx 9 RAW S.

% crossed relations: clauses for their own relations are added by dictionaries
pred neg-rel i:int, i:term, o:string.
neg-rel Ctx T S :- head T GR [_, A, B], gsuf "Logic.eq" GR, !,
  pp-rel Ctx " eq.not " A B S.


% STANDARD LIBRARY DICTIONARY
pred pp-app i:int, i:gref, i:list term, o:string.


% logic
pp-app Ctx GR [X] S :- gsuf "is_true" GR, !, pp Ctx X S.
pp-app Ctx GR [_, A, B] S :- gsuf "Logic.eq" GR, !, pp-rel Ctx " = " A B S.
pp-app Ctx GR [_, (fun N T Bo)] S :- gsuf "Logic.ex" GR, !,
  pp-ex Ctx (fun N T Bo) [] S.
pp-app Ctx GR [A, B] S :- gsuf "Logic.and" GR, !, pp-bin Ctx 6 " and " A B S.
pp-app Ctx GR [A, B] S :- gsuf "Logic.or"  GR, !, pp-bin Ctx 4 " or " A B S.
pp-app Ctx GR [A, B] S :- gsuf "Logic.iff" GR, !, pp-bin Ctx 2 " <==> " A B S.
pp-app Ctx GR [A] S :- gsuf "Logic.not" GR, !, pp-not Ctx A S.

% n-ary conjunction  [/\ ...]
pp-app Ctx GR [A, B, C] S :- gsuf "and3" GR, !, join-and [A, B, C] R, paren Ctx 6 R S.
pp-app Ctx GR [A, B, C, D] S :- gsuf "and4" GR, !,
  join-and [A, B, C, D] R, paren Ctx 6 R S.
pp-app Ctx GR [A, B, C, D, E] S :- gsuf "and5" GR, !,
  join-and [A, B, C, D, E] R, paren Ctx 6 R S.

% natural numbers
pp-app _ GR [] "0" :- gsuf "Datatypes.O" GR, !.
pp-app Ctx GR [N] S :- gsuf "Nat.pred" GR, !,    % predecessor  n.-1
  pp 21 N SN, RAW is SN ^ " - 1", paren Ctx 20 RAW S.
pp-app Ctx GR [N] S :- gsuf "Datatypes.S" GR, !,
  nat-lit (app [global GR, N]) C B,
  ( B = global GO, gsuf "Datatypes.O" GO, S is int_to_string C
  ; pp 41 B BS, CS is int_to_string C, RAW is BS ^ " + " ^ CS,
    paren Ctx 20 RAW S ), !.


% DEFINITION UNFOLDING AND GENERAL CASE
% named constants: printed from the const-notation table without unfolding.
% The subscripts are the last semantic arguments of the application
pp-app Ctx GR Args S :- const-notation Suf Base Style K, gsuf Suf GR,
  notation-args GR Args K Idx,
  render-const Ctx Base Style Idx S, !.

% an unknown transparent definition: unfold it and carry on.
% Dictionary clauses are inserted before this anchor.
:name "pp-app.fallback"
pp-app Ctx (const C) Args S :- coq.env.const C (some Body) _, !,
  coq.mk-app Body Args T, pp Ctx T S.

% constructor: the parameters of the inductive type are not printed
pp-app _ (indc K) Args S :- coq.env.indc K ParamNo _ _ _, ParamNo > 0,
  std.length Args L, L >= ParamNo, !,
  coq.gref->id (indc K) Id, std.drop ParamNo Args Fields,
  std.map Fields (a\ r\ pp 0 a r) RS, std.string.concat ", " RS AS,
  S is "op(\"" ^ Id ^ "\")(" ^ AS ^ ")".

% the general case of an application: the name as an operator
pp-app _ GR [] S :- !, coq.gref->id GR S.
pp-app _ GR Args S :- coq.gref->id GR Id,
  std.map Args (a\ r\ pp 41 a r) RS, std.string.concat " " RS AS,
  S is "op(\"" ^ Id ^ "\")(" ^ AS ^ ")".


% named constants
% Printing style: subscript form x_(k), functional form op("f")(x), or the
% base alone. With npartial the base is printed only under a partial
% application, since a full application is unfolded by its definition.
kind nstyle type.
type nsub nstyle.
type ncall nstyle.
type nbare nstyle.
type npartial nstyle.

% table: name suffix, displayed base, style, and the number of semantic
% arguments at the end of a full application. Clauses are added by the consumer
pred const-notation o:string, o:string, o:nstyle, o:int.

% the last semantic arguments of an application: the full arity is taken from
% the type of the constant, and the arguments hidden by hidden-var are dropped
pred notation-args i:gref, i:list term, i:int, o:list term.
notation-args GR Args K Idx :-
  coq.env.typeof GR Ty, prod-arity Ty M, std.length Args L,
  Take is L - M + K,
  take-last Take Args Idx0,
  std.filter Idx0 (a\ not (hidden-var a)) Idx.

pred prod-arity i:term, o:int.
prod-arity (prod N T F) M :- !,
  @pi-decl N T x\ prod-arity (F x) M0, M is M0 + 1.
prod-arity _ 0.

pred take-last i:int, i:list term, o:list term.
take-last K _ [] :- K =< 0, !.
take-last K L L :- std.length L Len, K >= Len, !.
take-last K L R :- std.length L Len, D is Len - K, std.drop D L R.

pred render-const i:int, i:string, i:nstyle, i:list term, o:string.
render-const _ Base nsub [] Base :- !.
render-const _ Base nsub Idx S :- !,
  std.map Idx (a\ r\ pp 0 a r) AS, std.string.concat "," AS J,
  subscript Base J S.
render-const _ Base ncall [] S :- !, S = Base.
render-const _ Base ncall Idx S :- !,
  std.map Idx (a\ r\ pp 0 a r) AS, std.string.concat ", " AS J,
  RAW is "(" ^ J ^ ")", S is "op(\"" ^ Base ^ "\")" ^ RAW.
render-const _ Base nbare _ Base :- !.
render-const _ Base npartial [] Base.


% auxiliary decompositions
% the qualifier of a predicate from a membership expression. The defining
% clause is added by the mathcomp dictionary
pred qualifier-of i:term, o:string.

% printing a qualifier: clauses for specific qualifiers are added by the
% dictionaries, and the general case prints the name as an operator
pred render-qual i:term, o:string.
:name "render-qual.fallback"
render-qual Q S :- head Q G _, coq.gref->id G Id, !,
  S is "op(\"" ^ Id ^ "\")".
render-qual Q S :- name-of Q Nm, !, q Nm S.

% the scrutinee is reduced to a constructor by unfolding definitions.
% Fixpoints are left folded, so that compact notation is not lost
pred scrut-constructor i:term, i:int, o:list term.
scrut-constructor T _ Args :- head T (indc _) Args, !.
scrut-constructor T D Args :- D > 0, head T (const C) CA,
  not (const-notation Suf _ _ _, gsuf Suf (const C)),
  coq.env.const C (some B) _, coq.mk-app B CA T1,
  peel-lets T1 T2, D1 is D - 1, scrut-constructor T2 D1 Args.

pred peel-lets i:term, o:term.
peel-lets (let _ _ V F) R :- !, peel-lets (F V) R.
peel-lets (app [let _ _ V F | Args]) R :- !,
  coq.mk-app (F V) Args R1, peel-lets R1 R.
peel-lets T T.

% unfold head constants that carry no notation of their own, so that the
% structural decomposition into summands and factors sees the term exactly as
% printing will see it. Structure operator heads are left folded. Clauses for
% their own operators are added by the dictionaries.
pred struct-head i:gref.
struct-head G :- gsuf "is_true" G.

pred expose i:term, o:term.
expose T T2 :- head T (const C) CA,
  not (struct-head (const C)),
  not (const-notation Suf _ _ _, gsuf Suf (const C)),
  coq.env.const C (some B) _, coq.mk-app B CA T1,
  peel-lets T1 T1p, !, expose T1p T2.
expose T T.

pred lam-arity i:term, o:int.
lam-arity (fun N T F) M :- !, @pi-decl N T x\ lam-arity (F x) M0, M is M0 + 1.
lam-arity _ 0.

pred is-bool-true i:term.
is-bool-true (global GR) :- gsuf "Datatypes.true" GR.
pred is-bool-false i:term.
is-bool-false (global GR) :- gsuf "Datatypes.false" GR.

% A Fixpoint recursion becomes a recurrence relation through a cases split on
% the recursion variable. The name and printing style of recursive occurrences
% are chosen from the gref of the enclosing definition, held by fix-display,
% whenever that gref is known.
pred fix-display o:gref.            % gref of the definition that set up the recursion

pred fix-mode i:name, o:rfmode.
fix-mode _ (rf-sub Base) :- fix-display GR,
  const-notation Suf Base nsub _, gsuf Suf GR, !.
fix-mode _ (rf-call FN) :- fix-display GR, !, coq.gref->id GR FN.
fix-mode N (rf-call FN) :- coq.name->id N FN.

pred fix-recurrence i:term, o:string.
fix-recurrence (fix N _ Ty Recf) S :- fix-mode N Mode,
  @pi-decl N Ty f\ (recfun f Mode :- !) => fix-args (Recf f) S.

pred fix-args i:term, o:string.
fix-args (fun Nm T F) S :- !,
  coq.name->id Nm V, @pi-decl Nm T x\ (name-of x V :- !) => fix-args (F x) S.
fix-args (match Sc _ [B0, BS]) S :- !,
  pp 0 Sc RecV, pp 0 B0 S0,
  ( BS = fun Np Tp Fp, coq.name->id Np P, q P QP,
    @pi-decl Np Tp p\ (name-of p P :- !) => pp 0 (Fp p) SS,
    Step is SS ^ " \"при\" " ^ RecV ^ " = " ^ QP ^ " + 1"
  ; pp 0 BS SS, Step is SS ),
  S is "cases(" ^ S0 ^ " \"при\" " ^ RecV ^ " = 0, " ^ Step ^ ")".
fix-args Other S :- pp 0 Other S.

% the branch condition: a choice operator is unfolded to its statement by the
% select-arg clause from a dictionary, otherwise the predicate itself is used,
% for example i = j
pred match-cond i:term, o:string.
match-cond Sc Cond :- select-arg Sc A, !, pp 0 A Cond.
match-cond Sc Cond :- pp 0 Sc Cond.

% a single-branch match decomposing a record: the fields are named by the
% binders of the branch, and the body is printed with those names.
pred match-record i:term, o:string.
match-record (fun N T F) S :- !,
  coq.name->id N V, @pi-decl N T x\ (name-of x V :- !) => match-record (F x) S.
match-record Body S :- pp 0 Body S.

% strip the leading lambdas of a branch, such as a sumbool proof binder
pred strip-lam i:term, o:term.
strip-lam (fun N T F) R :- !, @pi-decl N T x\ (name-of x "_" :- !) => strip-lam (F x) R.
strip-lam T T.

% a natural literal:  T = B + C successors, where B does not start with S
pred nat-lit i:term, o:int, o:term.
nat-lit (app [global GS, N]) C B :- gsuf "Datatypes.S" GS, !,
  nat-lit N C0 B, C is C0 + 1.
nat-lit T 0 T.

pred join-and i:list term, o:string.
join-and L R :- std.map L (t\ s\ pp 7 t s) Ss, std.string.concat " and " Ss R.

pred but-last i:list term, o:list term.
but-last [_] [] :- !.
but-last [X | Xs] [X | Ys] :- but-last Xs Ys.


% quantifiers with folded-in constraints
% A single constraint on a variable: a hypothesis or a conjunct stating that V
% satisfies a predicate. Its text is attached to the quantifier binder.
% Clauses of var-constraint1 for their own predicates are added by dictionaries.
pred var-constraint i:term, o:string, o:string.
var-constraint T Nm C :- unwrap-istrue T T1, var-constraint1 T1 Nm C.
pred var-constraint1 i:term, o:string, o:string.

% a binder with an annotation: a folded-in constraint or a domain taken from
% the type, where "" stands for the absence of an annotation
kind bnd type.
type bnd string -> string -> bnd.

pred bnd-get i:list bnd, i:string, o:string.
bnd-get [bnd V C | _] V C :- !.
bnd-get [_ | T] V C :- bnd-get T V C.
pred bnd-has i:list bnd, i:string.
bnd-has L V :- bnd-get L V _.

% binders: consecutive ones carrying the same annotation are merged, which
% gives x, y in RR instead of x in RR, y in RR
pred binders-str i:list bnd, o:string.
binders-str [] "" :- !.
binders-str [bnd V A | Rest] S :-
  same-ann A Rest Names Rest2,
  std.map [V | Names] q Qs, std.string.concat ", " Qs NJ,
  ( A = "", !, G = NJ ; G is NJ ^ " " ^ A ),
  ( Rest2 = [], !, S = G
  ; binders-str Rest2 S2, S is G ^ ", " ^ S2 ).

pred same-ann i:string, i:list bnd, o:list string, o:list bnd.
same-ann A [bnd V A | T] [V | Vs] Rest :- !, same-ann A T Vs Rest.
same-ann _ L [] L.

pred has-constr i:list bnd.
has-constr [bnd _ C | _] :- not (C = ""), !.
has-constr [_ | T] :- has-constr T.

% the range of a binder taken from its type, as a postfix to the name.
% Clauses for their own types are added by the dictionaries, and the core
% knows the naturals
pred type-domain i:term, o:string.
type-domain T S :- is-nat-type T, !,
  style-fmt "set-nat" [] S0, S is "in " ^ S0.


% common subterm extraction
% A long repeated subterm receives a label from style "cse-names", and its
% definition is moved into a caption after the statement, a line carrying the
% word from style "cse-where". A candidate is an application free of locally
% bound variables, no shorter than cse-min-len markup characters, occurring at
% least twice. The labels are installed by hypothetical pp clauses, so both
% printing and line breaking already see the shortened text.

kind cse type.
type cse term -> string -> cse.       % a term and its label

pred cse-min-len o:int.
:name "cse.default"
cse-min-len 30.

pred cse-max o:int.
cse-max 3.

% all application subterms: head constants without notation are unfolded, the
% way printing will unfold them, but at most cse-fuel times per statement,
% because unbounded unfolding blows up the size of the terms
pred cse-fuel o:int.
cse-fuel 40.

pred subterms i:term, i:list term, i:int, o:int, i:list sd, o:list sd,
  o:int.
subterms T0 Locals F0 F1 Acc Out Sz :- F0 > 0, head T0 (const C) CA,
  coq.env.const C (some B) _,
  not (struct-head (const C)),
  not (const-notation Suf _ _ _, gsuf Suf (const C)), !,
  Fm is F0 - 1, coq.mk-app B CA T1,
  subterms T1 Locals Fm F1 Acc Out Sz.
subterms (app L) Locals F0 F1 Acc Out Sz :- !,
  subterms-list L Locals F0 F1 Acc A1 Sz,
  ( Sz >= 8, ( Locals = [], ! ; not (has-local (app L) Locals) ), !,
    Out = [sd (app L) Sz | A1]
  ; Out = A1 ).
subterms (prod N T F) Locals F0 F1 Acc Out 1 :- !,
  subterms T Locals F0 Fa Acc A1 _,
  pi x\ subterms (F x) [x | Locals] Fa F1 A1 Out _.
subterms (fun N T F) Locals F0 F1 Acc Out 1 :- !,
  subterms T Locals F0 Fa Acc A1 _,
  pi x\ subterms (F x) [x | Locals] Fa F1 A1 Out _.
subterms (let _ _ V F) Locals F0 F1 Acc Out Sz :- F0 > 0, !,
  Fm is F0 - 1, subterms (F V) Locals Fm F1 Acc Out Sz.
subterms (let N T V F) Locals F0 F1 Acc Out 1 :- !,
  subterms T Locals F0 Fa Acc A1 _, subterms V Locals Fa Fb A1 A2 _,
  pi x\ subterms (F x) [x | Locals] Fb F1 A2 Out _.
subterms (match Sc R Br) Locals F0 F1 Acc Out 1 :- !,
  subterms Sc Locals F0 Fa Acc A1 _, subterms R Locals Fa Fb A1 A2 _,
  subterms-list Br Locals Fb F1 A2 Out _.
subterms (fix N _ T F) Locals F0 F1 Acc Out 1 :- !,
  subterms T Locals F0 Fa Acc A1 _,
  pi x\ subterms (F x) [x | Locals] Fa F1 A1 Out _.
subterms _ _ F F Acc Acc 1.

pred subterms-list i:list term, i:list term, i:int, o:int, i:list sd,
  o:list sd, o:int.
subterms-list [] _ F F Acc Acc 1 :- !.
subterms-list [T | Ts] Locals F0 F1 Acc Out Sz :-
  subterms T Locals F0 Fa Acc A1 S1,
  subterms-list Ts Locals Fa F1 A1 Out S2,
  Sz is S1 + S2.

pred has-local i:term, i:list term.
has-local T Locals :- std.exists Locals (x\ occurs-in x T).

pred occurs-in i:term, i:term.
occurs-in X X :- !.
occurs-in X (app L) :- !, std.exists L (t\ occurs-in X t).
occurs-in X (prod _ T F) :- !, ( occurs-in X T ; pi y\ occurs-in X (F y) ).
occurs-in X (fun _ T F) :- !, ( occurs-in X T ; pi y\ occurs-in X (F y) ).
occurs-in X (let _ T V F) :- !,
  ( occurs-in X T ; occurs-in X V ; pi y\ occurs-in X (F y) ).
occurs-in X (match Sc R Br) :- !,
  ( occurs-in X Sc ; occurs-in X R ; std.exists Br (t\ occurs-in X t) ).
occurs-in X (fix _ _ T F) :- !, ( occurs-in X T ; pi y\ occurs-in X (F y) ).

% grouping of occurrences by syntactic equality, comparing only terms with
% equal node counts, since this cheap test cuts the quadratic cost
kind sd type.
type sd term -> int -> sd.            % a subterm and its node count

kind cgrp type.
type cgrp term -> int -> cgrp.
pred cse-group i:list sd, o:list cgrp.
cse-group [] [] :- !.
cse-group [sd T Sz | Ts] [cgrp T C | Out] :-
  std.partition Ts (x\ sigma T2 S2\ x = sd T2 S2, S2 = Sz, T2 = T)
    Same Rest,
  std.length Same N, C is N + 1,
  cse-group Rest Out.

kind cm type.
type cm term -> int -> int -> cm.     % term, occurrences, markup length

pred cm-ge i:cm, i:cm.
cm-ge (cm _ _ L1) (cm _ _ L2) :- L1 >= L2.

% insertion sort by decreasing markup length
pred sort-cm i:list cm, o:list cm.
sort-cm [] [] :- !.
sort-cm [X | Xs] Out :- sort-cm Xs S1, insert-cm X S1 Out.
pred insert-cm i:cm, i:list cm, o:list cm.
insert-cm X [] [X] :- !.
insert-cm X [Y | Ys] [X, Y | Ys] :- cm-ge X Y, !.
insert-cm X [Y | Ys] [Y | Out] :- insert-cm X Ys Out.

% drop a candidate that occurs only inside an already accepted one
pred prune i:list cm, i:list cm, o:list cm.
prune [] _ [] :- !.
prune [cm T C L | Rest] Acc Out :-
  std.exists Acc (a\ sigma T2 L2\ a = cm T2 C L2, occurs-in T T2), !,
  prune Rest Acc Out.
prune [X | Rest] Acc [X | Out] :- prune Rest [X | Acc] Out.

pred take-n i:int, i:list cm, o:list cm.
take-n _ [] [] :- !.
take-n N _ [] :- N =< 0, !.
take-n N [X | Xs] [X | Ys] :- N1 is N - 1, take-n N1 Xs Ys.

% substring occurrence, avoiding regular expressions, since special characters
% of a pattern would break the parse
pred substr i:string, i:string.
substr S Sub :- LS is size S, LB is size Sub, LS >= LB,
  Max is LS - LB, substr-at S Sub LB 0 Max.
pred substr-at i:string, i:string, i:int, i:int, i:int.
substr-at S Sub LB I Max :- I =< Max,
  ( Sub is substring S I LB, ! ; I1 is I + 1, substr-at S Sub LB I1 Max ).

pred assign-names i:list cm, i:list string, o:list cse.
assign-names [] _ [] :- !.
assign-names _ [] [] :- !.
assign-names [cm T _ _ | Ts] [N | Ns] [cse T QN | Out] :-
  q N QN, assign-names Ts Ns Out.

% the type of an object candidate for extraction: carriers of structures and
% the naturals are known to the core, and clauses for their own types are
% added by the dictionaries
pred cse-obj-type i:term.
cse-obj-type T :- head T GTy _, gsuf ".sort" GTy.
cse-obj-type T :- is-nat-type T.

% selection: object terms only, excluding types, of length at least the
% threshold and with at least two occurrences. Larger ones come first, yet the
% clauses are added from smaller to larger, so that the definitions of the
% larger ones are printed through the smaller ones
pred cse-select i:list term, i:string, o:list cse.
cse-select Terms Plain Cands :-
  cse-fuel FU,
  std.fold Terms (pr FU []) (t\ a\ o\ sigma F0 A0 F1 A1 Sz\
    a = pr F0 A0, subterms t [] F0 F1 A0 A1 Sz, o = pr F1 A1) (pr _ All),
  cse-group All Groups,
  cse-min-len ML,
  std.map-filter Groups (g\ r\ sigma T C S L TyT\ g = cgrp T C,
    C >= 2,
    not (head T (indc _) _), not (head T (indt _) _),
    coq.typecheck T TyT ok,
    cse-obj-type TyT,
    pp 11 T S, L is size S, L >= ML,
    not (substr S "?"), not (substr S "Pack"),
    r = cm T C L) Meas,
  sort-cm Meas Sorted,
  prune Sorted [] Kept,
  cse-max MX, take-n MX Kept Top,
  style "cse-names" NS, rex.split " " NS Names0,
  std.filter Names0 (n\ not (substr Plain n)) Names,
  std.rev Top TopAsc,
  assign-names TopAsc Names Cands.

% add the substitution clauses and build the caption. The definition of each
% candidate is printed under the clauses of the smaller candidates
pred cse-render i:list cse, i:list string, i:list term, i:term, i:string,
  o:string.
cse-render [] ObjL HypL Concl Legend Out :-
  render-lines ObjL HypL Concl Legend Out.
cse-render [cse T Nm | Cs] ObjL HypL Concl LegAcc Out :-
  pp 11 T Def, style-fmt "cse-where" [] GDE,
  ( LegAcc = "", !,
    Leg2 is " \\ &" ^ GDE ^ " " ^ Nm ^ " = " ^ Def
  ; Leg2 is LegAcc ^ ", \\ &" ^ Nm ^ " = " ^ Def ),
  (pp _ T Nm :- !) => cse-render Cs ObjL HypL Concl Leg2 Out.


% statement quantifier walk
kind item type.

% variable name, constraint, and full text when the constraint is not folded in
type constr string -> string -> string -> item.
type ante term -> item.                   % a hypothesis as a term, its print
                                          % level set by the place of use

pred classify-hyp i:term, o:item.
classify-hyp T (constr Nm C Full) :- var-constraint T Nm C, !,
  q Nm QNm, Full is QNm ^ " " ^ C.
classify-hyp T (ante T).

% the nesting indent: D copies of "quad " before the content of a line, and a
% line break carrying that indent. At depth 0 the indent is empty, which keeps
% compatibility with the original single-position markup aligned on one & anchor
pred ind i:int, o:string.
ind 0 "" :- !.
ind D S :- D > 0, D1 is D - 1, ind D1 S0, S is "quad " ^ S0.
pred nl i:int, o:string.
nl D S :- ind D I, S is " \\ &" ^ I.

pred go i:term, i:list string, i:list term, o:string.
go (prod N T F) Objs Items Out :- is-field-type T, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => go (F x) Objs Items Out.
go (prod N T F) Objs Items Out :- is-nat-type T, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => go (F x) Objs Items Out.
go (prod N T F) Objs Hyps Out :- is-hyp N T, !,
  @pi-decl N T x\ go (F x) Objs [T | Hyps] Out.
go (prod N T F) Objs Hyps Out :- !,              % object binder
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => go (F x) [Nm | Objs] Hyps Out.
go Concl Objs Hyps Out :-
  std.rev Objs ObjL, std.rev Hyps HypL,
  assemble ObjL HypL Concl Out.

% take the first constraint of a given variable out of the hypothesis list
pred take-constr i:string, i:list item, o:string, o:list item.
take-constr O [constr O C _ | T] C T :- !.
take-constr O [X | T] C [X | T2] :- take-constr O T C T2.

% binders with constraints. Unused constraints go back into the hypothesis
% list as their full text
pred build-guards i:list string, i:list item, o:list bnd, o:list item.
build-guards [] Items [] Items :- !.
build-guards [O | Os] Items [bnd O C | Bs] Rest :-
  take-constr O Items C Items2, !, build-guards Os Items2 Bs Rest.
build-guards [_ | Os] Items Bs Rest :- build-guards Os Items Bs Rest.

pred build-antes i:list item, i:string, o:string.
build-antes [] Concl Concl :- !.
build-antes [ante H | T] Concl S :- !, build-antes T Concl S0,
  pp 1 H HS, S is HS ^ " => " ^ S0.
build-antes [constr _ _ Full | T] Concl S :- build-antes T Concl S0,
  S is Full ^ " => " ^ S0.

% assembly of a statement: a short one is printed on a single line, a long one
% goes line by line, with one hypothesis per line, a long conclusion broken
% separately and repeated subterms abbreviated. Lines are aligned through "\\ &"
pred assemble i:list string, i:list term, i:term, o:string.
assemble ObjL HypL Concl Out :-
  std.map HypL classify-hyp ItL,
  build-guards ObjL ItL Bs Rest,
  pp 0 Concl CS,
  build-antes Rest CS Body,
  ( Bs = [], !, Line = Body
  ; binders-str Bs BJ, Line is "forall " ^ BJ ^ ", " ^ Body ),
  layout-width W,
  ( size Line =< W, !, Out = Line
  ; ( cse-select [Concl | HypL] Line Cands, ! ; Cands = [] ),
    cse-render Cands ObjL HypL Concl "" Out ).

pred render-lines i:list string, i:list term, i:term, i:string, o:string.
render-lines ObjL HypL Concl Legend Out :-
  std.map HypL classify-hyp ItL,
  build-guards ObjL ItL Bs Rest,
  concl-lines 0 Concl CL,
  items-lines 0 Rest CL Body,
  ( Bs = [], !, Out0 is "&" ^ Body
  ; binders-str Bs BJ, Out0 is "&forall " ^ BJ ^ ", \\ &" ^ Body ),
  Out is Out0 ^ Legend.

% hypotheses one per line at depth D. A hypothesis is printed at level 0 and
% needs no surrounding parentheses: the line break and the trailing => already
% set it apart
pred items-lines i:int, i:list item, i:string, o:string.
items-lines _ [] Concl Concl :- !.
items-lines D [ante H | T] Concl S :- !, items-lines D T Concl S0,
  pp 0 H HS, nl D NL, S is HS ^ " =>" ^ NL ^ S0.
items-lines D [constr _ _ Full | T] Concl S :- items-lines D T Concl S0,
  nl D NL, S is Full ^ " =>" ^ NL ^ S0.

% a one-sided relation, for example the definiteness sign of a matrix: the
% clauses return the operand and the sign, and are added by the dictionaries
% and by the consumer
pred concl-oneside i:term, o:term, o:string.

% the conclusion: a long one is broken at the main relation, the right-hand
% side and the operand of a one-sided relation are broken at the top-level
% summands, and an existential is broken at the conjuncts of its body
pred concl-lines i:int, i:term, o:string.
concl-lines _ T Out :- layout-width W, pp 0 T S0, size S0 =< W, !, Out = S0.
concl-lines D T Out :- flatten-and T Conjs, Conjs = [_, _ | _], !,
  std.map Conjs (c\ r\ concl-lines D c r) RS,
  nl D NL, Sep is NL ^ "and ", std.string.concat Sep RS Out.
concl-lines D T Out :- T = prod _ _ _, !, forall-lines D T [] [] Out.
concl-lines D T Out :- unwrap-istrue T T0, expose T0 T1, rel-sides T1 Op A B, !,
  sum-lines D B SB,
  ( pp 11 A SA0, size SA0 =< 30, !,
    Out is SA0 ^ " " ^ Op ^ " " ^ SB
  ; sum-lines D A SA, nl D NL, Out is SA ^ NL ^ Op ^ " " ^ SB ).
concl-lines D T Out :- unwrap-istrue T T0, expose T0 T1,
  concl-oneside T1 M C, !,
  sum-lines D M SM, Out is SM ^ " " ^ C.
concl-lines D T Out :- expose T T1, head T1 GR [_, (fun N Ty Bo)],
  gsuf "Logic.ex" GR, !,
  pp-ex-lines D (fun N Ty Bo) [] Out.
concl-lines _ T Out :- pp 0 T Out.

% a long universal quantifier as a fragment: the line of binders, then the
% chain of hypotheses line by line, which is the idea of items-lines one level
% down. The binder walk repeats go, yet builds a fragment with no leading &
% and no common subterm extraction
pred forall-lines i:int, i:term, i:list string, i:list term, o:string.
forall-lines D (prod N T F) Objs Hyps Out :- is-field-type T, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => forall-lines D (F x) Objs Hyps Out.
forall-lines D (prod N T F) Objs Hyps Out :- is-nat-type T, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => forall-lines D (F x) Objs Hyps Out.
forall-lines D (prod N T F) Objs Hyps Out :- is-hyp N T, !,
  @pi-decl N T x\ forall-lines D (F x) Objs [T | Hyps] Out.
forall-lines D (prod N T F) Objs Hyps Out :- !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) =>
    forall-lines D (F x) [Nm | Objs] Hyps Out.
forall-lines D Concl Objs Hyps Out :-
  std.rev Objs ObjL, std.rev Hyps HypL,
  std.map HypL classify-hyp ItL,
  build-guards ObjL ItL Bs Rest,
  % the body indent deepens only when a binder is visible, since a hidden
  % binder without a constraint yields no forall line and hence no indent
  ( Bs = [], !, BD = D ; BD is D + 1 ),
  concl-lines BD Concl CL,
  items-lines BD Rest CL Body,
  ( Bs = [], !, Out = Body
  ; binders-str Bs BJ, nl BD NL, Out is "forall " ^ BJ ^ "," ^ NL ^ Body ).

% the main relation of a statement: clauses for their own relations are added
% by the dictionaries
pred rel-sides i:term, o:string, o:term, o:term.
rel-sides T "=" A B :- head T GR [_, A, B], gsuf "Logic.eq" GR, !.
rel-sides T "<==>" A B :- head T GR [A, B], gsuf "Logic.iff" GR, !.

% top-level summands start a new line when the sum does not fit on one line
kind addend type.
type addend string -> term -> addend.

pred sum-lines i:int, i:term, o:string.
sum-lines D B Out :- layout-width W, pp 11 B S0, size S0 > W,
  flatten-sum B [addend _ T1 | Rest], not (Rest = []), !,
  factor-lines D T1 S1 L1,
  pack-sum W D Rest S1 L1 Out.
sum-lines D B Out :- layout-width W, pp 11 B S0, size S0 > W, !,
  factor-lines D B Out _.
sum-lines _ B Out :- pp 11 B Out.

% greedy packing of summands: while a summand fits it stays on the same line,
% otherwise it moves to a new line indented to depth D. A long summand is
% broken along its factors
pred pack-sum i:int, i:int, i:list addend, i:string, i:int, o:string.
pack-sum _ _ [] Acc _ Acc :- !.
pack-sum W D [addend Sg T | Rest] Acc Cur Out :- pp 21 T ST, L is size ST,
  Cur2 is Cur + L + 3,
  ( Cur2 =< W, !, Acc2 is Acc ^ " " ^ Sg ^ " " ^ ST,
    pack-sum W D Rest Acc2 Cur2 Out
  ; factor-lines D T ST2 L2, nl D NL, Acc2 is Acc ^ NL ^ Sg ^ " " ^ ST2,
    L3 is L2 + 2, pack-sum W D Rest Acc2 L3 Out ).

% the inner factor of an adjoint: the clause is added by the mathcomp dictionary
pred adjoint-arg i:term, o:term.

% the matrix under a squared Frobenius norm. Clauses are added by the
% dictionaries and by the consumer, both for the trace form and for the named
% squared norm
pred frob-inner i:term, o:term.

% top-level factors: greedy packing across lines. A line break, indented to
% depth D, carries an explicit multiplication sign. The length of the last
% line is returned as well.
pred factor-lines i:int, i:term, o:string, o:int.
factor-lines D T Out LL :- layout-width W, pp 21 T S0, size S0 > W,
  flatten-mul T [F1 | Fs], not (Fs = []), !,
  pp 30 F1 S1, SZ1 is size S1,
  pack-factors W D Fs S1 SZ1 Out LL.

% a long Frobenius norm: break its interior along the top-level sum, so that
% norm(A - B)_F^2 moves a summand inside the brackets of the norm
factor-lines D T Out LL :- layout-width W, pp 21 T S0, size S0 > W,
  frob-inner T M, frob-break-inside tt, !,
  sum-lines D M SM, style-fmt "frob-sq" [SM] Out, LL is size Out.

% a long adjoint: break its interior along the top-level sum, which is
% disabled by default, see adjoint-break-inside.  (A + B)^* moves a summand
factor-lines D T Out LL :- layout-width W, pp 21 T S0, size S0 > W,
  adjoint-arg T M, adjoint-break-inside tt, !,
  sum-lines D M SM, style-fmt "adjoint" [] TR,
  Out is "(" ^ SM ^ ")" ^ TR, LL is size Out.
factor-lines _ T Out LL :- pp 21 T Out, LL is size Out.

pred pack-factors i:int, i:int, i:list term, i:string, i:int, o:string, o:int.
pack-factors _ _ [] Acc Cur Acc Cur :- !.
pack-factors W D [F | Fs] Acc Cur Out LL :- pp 31 F SF, L is size SF,
  Cur2 is Cur + L + 1,
  ( Cur2 =< W, !, Acc2 is Acc ^ " " ^ SF,
    pack-factors W D Fs Acc2 Cur2 Out LL
  ; nl D NL, Acc2 is Acc ^ NL ^ " dot " ^ SF, L2 is L + 4,
    pack-factors W D Fs Acc2 L2 Out LL ).

% decomposition of a product into factors: the clause for a matrix product is
% added by the mathcomp dictionary before the anchor
pred flatten-mul i:term, o:list term.
:name "flatten-mul.fallback"
flatten-mul T [T].

% decomposition of a sum into summands: the clauses for ring addition are
% added by the mathcomp dictionary before the anchor
pred flatten-sum i:term, o:list addend.
:name "flatten-sum.fallback"
flatten-sum T [addend "+" T].

% a conjunction as a list of conjuncts. The heads and, and3..5 flatten recursively
pred is-and-n i:gref.
is-and-n G :- gsuf "Logic.and" G.
is-and-n G :- gsuf "and3" G.
is-and-n G :- gsuf "and4" G.
is-and-n G :- gsuf "and5" G.

pred flatten-and i:term, o:list term.
flatten-and T L :- head T G Args, is-and-n G, !,
  std.map Args flatten-and Ls, flatten-concat Ls L.
flatten-and T [T].
pred flatten-concat i:list (list term), o:list term.
flatten-concat [] [].
flatten-concat [X | Xs] L :- flatten-concat Xs L0, std.append X L0 L.

% for every variable, take its first constraint out of the conjuncts. A
% constraint found this way overrides the domain given by the type
pred fold-conjs i:list bnd, i:list term, o:list bnd, o:list term.
fold-conjs [] Conjs [] Conjs :- !.
fold-conjs [bnd V _ | Vs] Conjs [bnd V C | Bs] Rest :-
  take-conj V Conjs C Conjs2, !, fold-conjs Vs Conjs2 Bs Rest.
fold-conjs [B | Vs] Conjs [B | Bs] Rest :- fold-conjs Vs Conjs Bs Rest.

pred take-conj i:string, i:list term, o:string, o:list term.
take-conj V [T | Ts] C Ts :- var-constraint T V C, !.
take-conj V [T | Ts] C [T | Ts2] :- take-conj V Ts C Ts2.

% a chain of existential quantifiers: collect the binders with their domains
% and fold in the constraints from the conjuncts of the body, where a
% constraint overrides the domain. The body follows " : " whenever the binders
% carry annotations
pred pp-ex i:int, i:term, i:list bnd, o:string.
pp-ex Ctx (fun N T Bo) Acc S :-
  coq.name->id N Nm,
  ( type-domain T Dom, ! ; Dom = "" ),
  @pi-decl N T x\ (name-of x Nm :- !) =>
    pp-ex-body Ctx (Bo x) [bnd Nm Dom | Acc] S.
pred pp-ex-body i:int, i:term, i:list bnd, o:string.
pp-ex-body Ctx B Acc S :- head B GR [_, (fun N T Bo)], gsuf "Logic.ex" GR, !,
  pp-ex Ctx (fun N T Bo) Acc S.

% a definition that unfolds to an existential quantifier continues the chain
pp-ex-body Ctx B Acc S :- head B (const C) CA, coq.env.const C (some Bo) _,
  coq.mk-app Bo CA B1, peel-lets B1 B2,
  head B2 GR [_, (fun N T Bo2)], gsuf "Logic.ex" GR, !,
  pp-ex Ctx (fun N T Bo2) Acc S.
pp-ex-body Ctx Body Acc S :- std.rev Acc Vars,
  flatten-and Body Conjs,
  fold-conjs Vars Conjs Bnds Rest,
  binders-str Bnds BJ,
  ( Rest = [], !, RAW is "exists " ^ BJ
  ; std.map Rest (t\ s\ pp 7 t s) RS, std.string.concat " and " RS RJ,
    ( has-constr Bnds, !, Sep = " : " ; Sep = ", " ),
    RAW is "exists " ^ BJ ^ Sep ^ RJ ),
  paren Ctx 0 RAW S.

% a chain of universal quantifiers: collect the consecutive object binders
% with their domains, then fold in the hypotheses that constrain one of the
% bound variables, where a constraint overrides the domain given by the type
pred pp-forall i:int, i:term, i:list bnd, o:string.
pp-forall Ctx (prod N T F) Acc S :- not (is-hyp N T), !,
  coq.name->id N Nm,
  ( type-domain T Dom, ! ; Dom = "" ),
  @pi-decl N T x\ (name-of x Nm :- !) =>
    pp-forall Ctx (F x) [bnd Nm Dom | Acc] S.
pp-forall Ctx Body Acc S :- std.rev Acc Vars, pp-forall2 Ctx Vars [] Body S.

pred pp-forall2 i:int, i:list bnd, i:list bnd, i:term, o:string.
pp-forall2 Ctx Vars Found (prod N T F) S :- is-prop T,
  var-constraint T V C, bnd-has Vars V, not (bnd-has Found V), !,
  @pi-decl N T h\ pp-forall2 Ctx Vars [bnd V C | Found] (F h) S.
pp-forall2 Ctx Vars Found Body S :-
  pp 0 Body SB,
  merge-bnds Vars Found Bnds,
  binders-str Bnds BJ,
  RAW is "forall " ^ BJ ^ ", " ^ SB, paren Ctx 0 RAW S.

pred merge-bnds i:list bnd, i:list bnd, o:list bnd.
merge-bnds [] _ [].
merge-bnds [bnd V _ | Vs] Found [bnd V C | Bs] :- bnd-get Found V C, !,
  merge-bnds Vs Found Bs.
merge-bnds [B | Vs] Found [B | Bs] :- merge-bnds Vs Found Bs.

% an existential chain with the conjuncts of the body one per line. Each
% conjunct is broken like a conclusion when that is needed
pred pp-ex-lines i:int, i:term, i:list bnd, o:string.
pp-ex-lines D (fun N T Bo) Acc S :-
  coq.name->id N Nm,
  ( type-domain T Dom, ! ; Dom = "" ),
  @pi-decl N T x\ (name-of x Nm :- !) =>
    pp-ex-lines-body D (Bo x) [bnd Nm Dom | Acc] S.
pred pp-ex-lines-body i:int, i:term, i:list bnd, o:string.
pp-ex-lines-body D B Acc S :- head B GR [_, (fun N T Bo)],
  gsuf "Logic.ex" GR, !, pp-ex-lines D (fun N T Bo) Acc S.
pp-ex-lines-body D B Acc S :- head B (const C) CA,
  coq.env.const C (some Bo) _, coq.mk-app Bo CA B1, peel-lets B1 B2,
  head B2 GR [_, (fun N T Bo2)], gsuf "Logic.ex" GR, !,
  pp-ex-lines D (fun N T Bo2) Acc S.
pp-ex-lines-body D Body Acc S :- std.rev Acc Vars,
  flatten-and Body Conjs,
  fold-conjs Vars Conjs Bnds Rest,
  binders-str Bnds BJ,
  ( Rest = [], !, S is "exists " ^ BJ
  ; D1 is D + 1, nl D1 NL,
    std.map Rest (t\ r\ concl-lines D1 t r) RS,
    Sep is NL ^ "and ", std.string.concat Sep RS RJ,
    S is "exists " ^ BJ ^ " :" ^ NL ^ RJ ).

% a definition  LHS := RHS  : the left-hand side is the name applied to the
% object parameters, and the body is printed as the right-hand side, with the
% type and the dimensions dropped.
pred def-go i:gref, i:term, i:list string, o:string.
def-go GR (fun N T F) Names S :- is-field-type T, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => def-go GR (F x) Names S.
def-go GR (fun N T F) Names S :- is-nat-type T, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => def-go GR (F x) Names S.
def-go GR (fun N T F) Names S :- is-prop T, !,   % proof parameter
  @pi-decl N T x\ def-go GR (F x) Names S.
def-go GR (fun N T F) Names S :- T = sort _, !,  % type parameter
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => def-go GR (F x) Names S.
def-go GR (fun N T F) Names S :-                 % instance of an operations class
  head T HG _, gsuf "_of" HG, !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => def-go GR (F x) Names S.
def-go GR (fun N T F) Names S :- !,
  coq.name->id N Nm,
  @pi-decl N T x\ (name-of x Nm :- !) => def-go GR (F x) [Nm | Names] S.
def-go GR Body Names S :-
  coq.gref->id GR Id, std.rev Names NL, std.map NL q NLq,
  ( NLq = [], LHS is "op(\"" ^ Id ^ "\")"
  ; std.string.concat ", " NLq PJ, LHS is "op(\"" ^ Id ^ "\")(" ^ PJ ^ ")" ),
  (fix-display GR :- !) => pp 0 Body RHS,
  Line is LHS ^ " := " ^ RHS,
  layout-width W,
  ( size Line =< W, !, S = Line
  ; (fix-display GR :- !) =>
      ( is-prop Body, !, concl-lines 0 Body RHS2 ; sum-lines 0 Body RHS2 ),
    S is "&" ^ LHS ^ " := \\ &" ^ RHS2 ).

% Rendering driven by the kind of declaration: a definition through its body
% LHS := RHS, a record with a single constructor as a tuple of fields, and
% everything else through the type of the statement. The body is taken only
% from a transparent constant.
pred render-gref i:string, i:gref, o:string.
render-gref "def" (const C) S :- coq.env.const C (some Body) _, !,
  def-go (const C) Body [] S.
render-gref "def" (indt I) S :- coq.env.indt I _ _ _ _ [_] [KTy], !,
  coq.gref->id (indt I) Id,
  ctor-fields KTy Fields, std.map Fields q Qs,
  std.string.concat ", " Qs FJ,
  S is "op(\"" ^ Id ^ "\") := (" ^ FJ ^ ")".
render-gref _ GR S :- coq.env.typeof GR Ty, go Ty [] [] S.

% names of the record fields: the binders of the constructor type, with the
% parameters left out
pred ctor-fields i:term, o:list string.
ctor-fields (prod N T F) Out :-
  ( is-field-type T ; is-nat-type T ; T = sort _ ), !,
  @pi-decl N T x\ ctor-fields (F x) Out.
ctor-fields (prod N T F) [Nm | Out] :- !, coq.name->id N Nm,
  @pi-decl N T x\ ctor-fields (F x) Out.
ctor-fields _ [].


% JSON output
pred json-escape i:string, o:string.
json-escape S O :- rex.replace "\\\\" "\\\\\\\\" S O1,
  rex.replace "\"" "\\\"" O1 O.

% the list of statements to print: module, kind, which is either "def" or
% "lemma", and name. Clauses are added by the consumer, and the order of the
% clauses fixes the order in the JSON
pred target o:string, o:string, o:string.

pred first-gref i:list located, o:gref.
first-gref [loc-gref GR | _] GR :- !.
first-gref [_ | T] GR :- first-gref T GR.

% The gref is looked up by the qualified name module.name first, because local
% abbreviations introduced by Local Notation shadow unqualified constant names.
pred render-one i:string, i:string, i:string, o:string. % -> "key": "value"
render-one Mod Kind Name S :-
  ( rex.split "/" Mod Segs, std.last Segs M1, LocName is M1 ^ "." ^ Name,
    coq.locate-all LocName L, first-gref L GR, render-gref Kind GR V0, !
  ; coq.locate-all Name L2, first-gref L2 GR2, render-gref Kind GR2 V0, !
  ; V0 = "?" ),
  format-idents V0 V, json-escape V VE, Key is Mod ^ "." ^ Name,
  json-escape Key KE, S is "  \"" ^ KE ^ "\": \"" ^ VE ^ "\"".

}}.

(*
  The RenderTypst command prints every target clause of the typst.db database
  and writes JSON. The output path is the first string argument of the command,
  otherwise the ROCQ2TYPST_OUT environment variable.
*)
Elpi Command RenderTypst.
Elpi Accumulate Db typst.db.
Elpi Accumulate lp:{{

pred out-path i:list argument, o:string.
out-path [str Path | _] Path :- !.
out-path _ Path :- getenv "ROCQ2TYPST_OUT" (some Path).

:name "main.run"
main Args :-
  std.findall (target M_ K_ N_) TS,
  std.map TS (t\ s\ sigma M K N\ t = target M K N, render-one M K N s) Frags,
  std.string.concat ",\n" Frags Body,
  Json is "{\n" ^ Body ^ "\n}\n",
  ( out-path Args Path, !,
    open_out Path OC, output OC Json, close_out OC,
    coq.say "rocq2typst: wrote" Path
  ; coq.say "rocq2typst: no output path given, file not written"
  ).

}}.

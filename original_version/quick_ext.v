
(** An attempt to streamline VV’s proof of functional extensionality, from the Univalence axiom plus the eta-rule.  Using ideas coming from VV, SA, AB, & others… *)

(** The outline of this proof:

(1) The basic definition of path spaces.  (And various workhorse functions on paths: composition, transport, congruence, etc.)

(2) The Univalence axiom.  (Preceded by some homotopical concepts, defining weak equivalences, etc.)

(3) The recursion principle for weak equivalences, transported via Univalence from the analogous recursor on paths.  (Preceded by a few lemmas.)

(4a) A not terribly interesting lemma, with an essentialy routine but very lengthy proof: if a function is pointwise equal to the identity, then it is a weak equivalence.

(4) etaAxiom: (fun x => f x) ~ f.  (VV’s etacorrection)  Hence, by preceding lemma, eta-expansion is a weak equivalence.  (This section and (4a) do not use Univalence.)

(5) If w : X -> Y is a Weq, then so is precomposition with w,  (w o -) : (A -> X) -> (A -> Y).
Easy given that we have (3) and (4).

(6) Total path spaces  TotPaths X := { x, x' : X  &  p : X ~ x' }  and the fact that src and tgt from these are equivalences.

(7) Putting all these together: fext!  The argument for fext given these:
given functions  f,g : X -> Y  and pointwise equality  alpha: forall x, f x ~ g x,
consider two elements of X -> TotPaths Y:
  (fun x => (f x, f x, refl))
  (fun x => (f x, g x, alpha x))
When composed with src, these both give f, so are ‘equal’.  But composition with src is a Weq; so precomposition with it is a Weq; so these were already ‘equal’ in  X -> TotPaths Y.  But composing these with tgt gives (eta-expansions of) f and g; so f and g are equal in X -> Y.
*)



(** for the sake of readability, I’m not using VV’s roll-your-own sigma-types, but sticking with Coq’s own (which, as I understand, are equivalent under the hood, except possibly as regards universe issues, which are not of importance here). *)



(** Path spaces, and basic lemmas about them. *)

Inductive Paths {X:Type} : X -> X -> Type :=
  | refl {x:X} : Paths x x.

Notation "x ~ y" := (Paths x y) (at level 50) : type_scope.

Definition sym {X:Type} {x y : X} (p : x ~ y) : y ~ x :=
match p with refl x => refl end.

Definition symIsInvol  {X:Type} {x y : X} (p : x ~ y)
              : sym (sym p) ~ p.
induction p; simpl.  exact refl.
Defined.

Definition trans {X:Type} {x y z : X} (p : x ~ y) (q : y ~ z) : x ~ z.
induction p.  exact q.
Defined.

Definition symSwitchesTrans {X:Type} {x y z : X} (p : x ~ y) (q : y ~ z)
               : sym (trans p q) ~ trans (sym q) (sym p).
induction p.  induction q.  simpl.  exact refl.
Defined.

Definition transIsAssoc {X:Type} {x y z w : X} (p:x~y) (q:y~z) (r:z~w) 
               : trans (trans p q) r ~ trans p (trans q r).
induction p; induction q; induction r; simpl.  exact refl.
Defined. 

Definition transRightUnit {X:Type} {x y: X} (p:x~y) 
               : trans p refl ~ p.
induction p; simpl.  exact refl.
Defined. 

Definition transLeftUnit {X:Type} {x y: X} (p:x~y) 
               : trans refl p ~ p.
induction p; simpl.  exact refl.
Defined. 

Definition symLeftInverse {X:Type} {x y: X} (p:x~y)
               : trans (sym p) p ~ refl.
induction p; simpl.  exact refl.
Defined.

Definition symRightInverse {X:Type} {x y: X} (p:x~y)
               : trans p (sym p) ~ refl.
induction p; simpl.  exact refl.
Defined.


Definition transport {X:Type} (P: X -> Type) {x x':X} (p: x ~ x') : P x -> P x'.
induction p.  exact (fun y => y).
Defined.

Definition cong {X Y:Type} (f: X -> Y) {x x' : X} (p: x ~ x') : f x ~ f x'.
induction p.  exact refl.
Defined.

Definition congPreservesTrans {X Y:Type} (f: X -> Y) {x y z : X} 
             (p: x ~ y) (q: y ~ z) : (cong f (trans p q)) ~ trans (cong f p) (cong f q).
induction p.  induction q.  simpl.  exact refl.
Defined.

Definition congPreservesSym {X Y:Type} (f: X -> Y) {x y : X} 
             (p: x ~ y) : (cong f (sym p)) ~ sym (cong f p).
induction p.  simpl.  exact refl.
Defined.


(* Some constructions on sigma types and paths *)

Definition pair {X:Type} {P:X->Type} (x:X) (y:P x) := existT P x y.

Definition pairPath {X:Type} {P: X -> Type} {x x' : X} (p : x ~ x') :
             forall {y : P x} {y' : P x'} (q : (transport P p y) ~ y'), 
                  (pair x y) ~ (pair x' y').
induction p. simpl.  intros y y' q; induction q.  exact refl.
Defined.




(** Some homotopical concepts; a streamlined lead up to the univalence axiom. *)

Definition isContr (X:Type) : Type := sigT (fun x:X => forall y:X, y~x).

Definition Fiber {X Y:Type} (f:X -> Y) (y:Y) := sigT (fun x:X => (f x) ~ y).

Definition isWeq {X Y:Type} (f:X -> Y) := forall y:Y, isContr (Fiber f y).

Definition Weq (X Y:Type) := sigT (fun f : X->Y => isWeq f).

Definition PathsTo {X:Type} (x:X) := sigT (fun y:X => y ~ x).

Definition reflTo {X:Type} (x:X) : PathsTo x
  := (pair (P := (fun y:X => y ~ x)) x refl).

Lemma x_refl_central {X:Type} : forall (x:X) (yp: PathsTo x), yp ~ reflTo x.
intros x yp.  destruct yp as [ y pyx ].  unfold reflTo.  elim pyx.
exact (fun x => refl).
Qed.

Lemma idIsWeq {X:Type} : isWeq (fun x:X => x).
intros x.  exact (pair (reflTo x) (x_refl_central x)).
Qed.

Definition pathToWeq {X Y : Type} (p : X ~ Y) : Weq X Y.
destruct p as [ X ].  exact (pair (fun x:X => x) idIsWeq).
Defined.

(* This throws a universe inconsistency if we fixed the universe to start with, since we are trying to use Paths Type X Y. *)

Axiom univalence : forall {X Y : Type}, isWeq (pathToWeq (X:=X) (Y:=Y)). 






(* Some lemmas about weak equivalences, as needed to prove an induction principle for Weq’s, analogous to that for paths, using univalence. *)

Definition WkInv {X Y : Type} (f : X -> Y) := 
              { g: Y -> X
              & { eta : forall (x:X), x ~ g (f x) 
                &       forall (y:Y), f (g y) ~ y } }.

Definition IsWeqToReturn {X Y : Type} (w : Weq X Y) : Y -> X.
unfold Weq, isWeq, isContr in w.
intros y.  destruct w as [f h].  destruct (h y) as [[x p] k].
exact x.
Defined.

Definition WeqToFun {X Y : Type} (w : Weq X Y) : X -> Y.
destruct w as [f k].  exact f.
Defined.

Definition IsSectionReturn {X Y : Type} (w : Weq X Y) (y:Y) : ((WeqToFun w) ((IsWeqToReturn w) y)) ~ y. 
destruct w as [f k].
unfold isWeq, isContr in k.
unfold IsWeqToReturn.  simpl.
destruct (k y) as [[x p] l].
exact p.
Defined.

Definition weqToPath {X Y : Type} : Weq X Y -> X ~ Y.
apply IsWeqToReturn.
exact (pair pathToWeq univalence).
Defined.

Definition weqToPathIsSection {X Y : Type} (w : Weq X Y) : (pathToWeq (weqToPath w)) ~ w.
unfold weqToPath.
exact (IsSectionReturn (pair pathToWeq univalence) w).
Defined.




(* A recursor for Weq. *)
(* This is probably the single most important step. *)

Lemma predOnWeqToPredOnPath (P : forall X Y : Type, (Weq X Y) -> Type)
           : forall X Y : Type, Paths X Y -> Type.
exact (fun X Y p => P X Y (pathToWeq p)).
Defined.


Lemma Weq_rec (P : forall X Y : Type, (Weq X Y) -> Type)
      (D : (forall X : Type, P X X (pair (fun x:X => x) idIsWeq)))
      : forall (X Y : Type) (w : Weq X Y), P X Y w.
pose (P' := predOnWeqToPredOnPath P).
assert (D' : forall X : Type, (P'  X X refl)).
intros X.  unfold P', predOnWeqToPredOnPath, pathToWeq.
exact (D X).
intros X Y w.
assert (Concl' := Paths_rect Type P' D' X Y (weqToPath w)).
unfold P', predOnWeqToPredOnPath in Concl'.
assert (w_coerce := weqToPathIsSection w).
pose (w' :=  pathToWeq (weqToPath w)).
replace (pathToWeq (weqToPath w)) with w' in * |- *; try reflexivity.
exact (transport (X := Weq X Y) (fun (v:Weq X Y) => P X Y v) w_coerce Concl'). 
Defined.






(* a useful lemma which requires a long chain of two-dimensional reasoning *)
(* this is very lengthy but essentially routine; could presumably be greatly
shortened by a well-written tactic or two *)
 
Lemma pointwiseIdIsWeq {X : Type} (f : X -> X) (alpha : forall x:X, f x ~ x) : isWeq f.
intros x0.  split with (existT (fun x => f x ~ x0) x0 (alpha x0)).  intros [y p]. 
apply sym. pose (ay_sp := (trans (sym p) (alpha y))).
apply (pairPath (P := (fun x : X => f x ~ x0)) ay_sp).

assert (transportIsComp : forall {z z' : X} (q : z ~ z') (p : f z ~ x0),
           (transport (fun x : X => f x ~ x0) q p) ~ (trans (sym (cong f q)) p)).
clear y p ay_sp.  intros z z' q; induction q as [z].  intros p; simpl; apply refl.
apply (trans (transportIsComp _ _ ay_sp (alpha x0))).  clear transportIsComp.

assert (step : trans (sym (cong f ay_sp)) (alpha x0)
              ~ trans (sym (trans (cong f (sym p)) (cong f (alpha y)))) (alpha x0) ).
apply (cong (fun q => trans (sym q) (alpha x0))).  exact (congPreservesTrans f (sym p) (alpha y)).
apply (trans step).  clear ay_sp step.

assert (step :  trans (sym (trans (cong f (sym p)) (cong f (alpha y)))) (alpha x0)
                ~  trans (sym (trans (sym (cong f p)) (cong f (alpha y)))) (alpha x0)).
apply (cong (fun q => trans (sym (trans q (cong f (alpha y)))) (alpha x0))).
exact (congPreservesSym f p).
apply (trans step).  clear step.

assert (step :  trans (sym (trans (sym (cong f p)) (cong f (alpha y)))) (alpha x0)
                ~ trans ( trans (sym (cong f (alpha y))) (sym (sym (cong f p)))) (alpha x0)).
apply (cong (fun q => trans q (alpha x0))). 
exact (symSwitchesTrans _ _).
apply (trans step).  clear step.

assert (step :  trans (trans (sym (cong f (alpha y))) (sym (sym (cong f p)))) (alpha x0)
                ~ trans (trans (sym (cong f (alpha y))) (cong f p)) (alpha x0)).
apply (cong (fun q => trans (trans (sym (cong f (alpha y))) q) (alpha x0))).
exact (symIsInvol _).
apply (trans step).  clear step.

assert (step :  trans (trans (sym (cong f (alpha y))) (cong f p)) (alpha x0)
                ~  trans (sym (cong f (alpha y))) (trans (cong f p) (alpha x0))).
exact (transIsAssoc _ _ _).
apply (trans step).  clear step.

assert (natOfAlpha : forall (z z':X) (q : z ~ z'),
            (trans (cong f q) (alpha z')) ~ (trans (alpha z) q)).
intros z z' q; induction q as [z]; simpl.  exact (sym (transRightUnit _)).

assert (step : trans (sym (cong f (alpha y))) (trans (cong f p) (alpha x0))
               ~   trans (sym (cong f (alpha y))) (trans (alpha (f y)) p)).
apply (cong (trans (sym (cong f (alpha y))))).  exact (natOfAlpha _ _ _).
apply (trans step).  clear step.

assert (step : trans (sym (cong f (alpha y))) (trans (alpha (f y)) p)
               ~ trans (trans (sym (cong f (alpha y))) (alpha (f y))) p).
exact (sym (transIsAssoc _ _ _)).
apply (trans step).  clear step.

assert (step : trans (trans (sym (cong f (alpha y))) (alpha (f y))) p
               ~ trans (trans (cong f (sym (alpha y))) (alpha (f y))) p).
apply (cong (fun q => trans (trans q (alpha (f y))) p)).
exact (sym (congPreservesSym _ _)).
apply (trans step).  clear step.

assert (step : trans (trans (cong f (sym (alpha y))) (alpha (f y))) p
               ~  trans (trans (alpha y) (sym (alpha y))) p).
apply (cong (fun q =>  trans q p)).  
exact (natOfAlpha _ _ _).
apply (trans step).  clear step.

assert (step : trans (trans (alpha y) (sym (alpha y))) p
               ~ trans refl p).
apply (cong (fun q => trans q p)).
exact (symRightInverse _).
apply (trans step).  clear step.

(* here one might need reflLeftUnit if trans were implemented differently *)
simpl.  exact refl.
Qed.





(** The other axiom we need: VV’s “eta-correction”, a propositional eta-rule.
    From this, the proof that eta-expansion is a Weq.
    (No univalence required here.) *)

Definition etaExp {X Y : Type} (f : X -> Y) := (fun x => f x).

Axiom etaAxiom : forall {X Y : Type} (f : X -> Y), (etaExp f) ~ f.

Lemma etaExpIsWeq {X Y : Type} : isWeq (etaExp (X:=X) (Y:=Y)).
exact (pointwiseIdIsWeq etaExp etaAxiom).
Qed.


(* A lemma about Weq’s, then the fact that postcomposition with a Weq is a Weq. *)
(* Easy now we have the induction principle and etaExpIsWeq. *)

Lemma WeqsExponentiate {X Y Z: Type} (w : Weq Y Z) : isWeq (fun (f:X->Y) => (fun x => (WeqToFun w) (f x))). 
generalize Y Z w. clear Y Z w.
apply Weq_rec.  intros Y.  simpl.  exact etaExpIsWeq.
Qed.



(* Total path spaces, X.X.Id_X, and the equivalences src, tgt from this to X. *)

Definition TotPaths (X:Type) := (sigT (fun x:X => (sigT (fun y:X => x~y)))).

Definition reflTot {X:Type} (x:X) : TotPaths X
  := pair x (pair x refl).

Definition src {X:Type} (xyp:TotPaths X) : X.
destruct xyp as [x yp].  exact x.
Defined.

Definition tgt {X:Type} (xyp:TotPaths X) : X.
destruct xyp as [x yp]; destruct yp as [y pxy].  exact y.
Defined.

Lemma srcIsWeq {X:Type} : isWeq (src (X:=X)).
intros x.  unfold isContr.
assert (xxrr : Fiber src x).  unfold Fiber, src, TotPaths.
apply (existT (fun (x0:{x0 : X & {y : X & x0 ~ y}}) => ((let (x1, _) := x0 in x1) ~ x)) (pair x (pair x refl))).
simpl.  apply refl.
split with xxrr.
intros y.  unfold Fiber, src, TotPaths in y. 
destruct y as [[a [b p] ] q].  destruct p as [a].  destruct q as [x].
destruct xxrr as [[a [b p] ] q].  destruct p as [a].  simpl in q. destruct q as [x].
exact refl.
Qed.

Lemma tgtIsWeq {X:Type} : isWeq (tgt (X:=X)).
intros x.  unfold isContr.
assert (xxrr : Fiber tgt x).  unfold Fiber, tgt, TotPaths.
apply (existT (fun (x0:{x0 : X & {y : X & x0 ~ y}}) => (let (x1, yp) := x0 in let (y, _) := yp in y) ~ x)
          (pair x (pair x refl))).
simpl.  apply refl.
split with xxrr.
intros y.  unfold Fiber, src, TotPaths in y. 
destruct y as [[a [b p] ] q].  destruct p as [a].  simpl in q. destruct q as [x].
destruct xxrr as [[a [b p] ] q].  destruct p as [a].  simpl in q. destruct q as [x].
exact refl.
Qed.

Lemma weqIsInjective {X Y:Type} (w:Weq X Y) {x x':X}
           : ((WeqToFun w x) ~ (WeqToFun w x'))  ->  (x ~ x').
destruct w as [f v]; simpl.  intros q.
destruct (v (f x')) as [[x0 p0] k].
pose (xq := pair (P:=(fun z => (f z ~ f x'))) x q).
pose (x'r := pair (P:=(fun z => (f z ~ f x'))) x' refl).
assert (xq ~ x'r) as xq_x'r.
exact (trans (k xq) (sym (k x'r))).
exact (cong (X:=Fiber f (f x')) (Y:=X) 
            (projT1 (A:=X) (P:=(fun z => f z ~ f x')))
            xq_x'r).
Defined.


Definition fext {X Y:Type} {f g:X -> Y} (alpha : forall x:X, f x ~ g x) : f ~ g.
pose (ffrf := (fun x => reflTot (f x)) : X -> TotPaths Y).
pose (fgalpha := (fun x => (pair (f x) (pair (g x) (alpha x)))) : X -> TotPaths Y).
pose (src_o_ := (fun (h:X->TotPaths Y) => (fun x => (src (h x))))).
pose (src_o_isWeq := WeqsExponentiate (X := X) (pair (src (X:=Y)) (srcIsWeq (X:=Y)))
         : isWeq (src_o_) ).
assert (ffrf ~ fgalpha) as ffrf_to_fgalpgha.
apply (weqIsInjective (pair src_o_ src_o_isWeq)).
simpl.  unfold src_o_, ffrf, fgalpha; simpl.  exact refl.
clear src_o_ src_o_isWeq.
pose (tgt_o_ := (fun (h:X->TotPaths Y) => (fun x => (tgt (h x))))).
pose (doneUpToEta := cong tgt_o_ ffrf_to_fgalpgha).
unfold tgt_o_, ffrf, fgalpha, tgt in doneUpToEta; simpl in doneUpToEta.
exact (trans (sym (etaAxiom f)) (trans doneUpToEta (etaAxiom g))).
Defined.















(*
Some lemmas written earlier but not currently needed:

Lemma transportIsWeq {X : Type} (P : X -> Type) {x x' : X} (w: x ~ x') : isWeq (transport P w).
induction w.  simpl.  exact idIsWeq.
Qed.

Lemma weqToContrIsContr {X Y : Type} (f : X -> Y) (v : isWeq f) (xalpha : isContr X) : isContr Y. 
(** It’s awfully tempting to cheat and just use univalence here: “by induction, X = Y, done!”
  But univalence is not actually required, so let’s be patient. *)
destruct xalpha as [x alpha].  unfold isContr.
split with (f x).  intros y.
destruct (v y) as [[x' p] k]; clear k.
exact (trans (sym p) (cong f (alpha x'))).
Qed.
*)

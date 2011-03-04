Require Import paths.


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

(*
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
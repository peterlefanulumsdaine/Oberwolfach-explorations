Require Import paths.
Require Import basic_weqs.

(** The other axiom we need: VV’s “eta-correction”, a propositional eta-rule.
    From this, the proof that eta-expansion is a Weq.
    (Note: no univalence required here.) *)

Definition etaExp {X Y : Type} (f : X -> Y) := (fun x => f x).

Axiom etaAxiom : forall {X Y : Type} (f : X -> Y), (etaExp f) ~ f.

Lemma etaExpIsWeq {X Y : Type} : isWeq (etaExp (X:=X) (Y:=Y)).
exact (pointwiseIdIsWeq etaExp etaAxiom).
Qed.
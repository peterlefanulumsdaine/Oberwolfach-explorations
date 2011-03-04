(** Includes the univalence axiom, and the definition from it of the induction principle for weak equivalences. *)

Require Import paths.
Require Import basic_weqs.



(* NB This would throw a universe inconsistency if we had fixed just one universe to start with, since we are trying to use Paths Type X Y, i.e. paths in some universe. *)

Axiom univalence : forall {X Y : Type}, isWeq (pathToWeq (X:=X) (Y:=Y)). 



Definition weqToPath {X Y : Type} : Weq X Y -> X ~ Y.
  apply IsWeqToReturn.
  exact (pair pathToWeq univalence).
Defined.

Definition weqToPathIsSection {X Y : Type} (w : Weq X Y) : (pathToWeq (weqToPath w)) ~ w.
  unfold weqToPath.  exact (IsSectionReturn (pair pathToWeq univalence) w).
Defined.



(* A recursor for Weq. *)
(* This is probably the single most important step. *)

Definition predOnWeqToPredOnPath (P : forall X Y : Type, (Weq X Y) -> Type)
           : forall X Y : Type, Paths X Y -> Type.
  exact (fun X Y p => P X Y (pathToWeq p)).
Defined.


Definition Weq_rec (P : forall X Y : Type, (Weq X Y) -> Type)
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


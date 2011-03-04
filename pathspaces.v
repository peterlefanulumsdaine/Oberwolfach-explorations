
Require Import paths.
Require Import basic_weqs.


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



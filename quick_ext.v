Require Import paths.
Require Import basic_weqs.
Require Import pathspaces.
Require Import etacorrection.
Require Import univalence.


(* A lemma about Weq’s, then the fact that postcomposition with a Weq is a Weq. *)
(* Easy, given the induction principle and etaExpIsWeq. *)

Lemma WeqsExponentiate {X Y Z: Type} (w : Weq Y Z) : isWeq (fun (f:X->Y) => (fun x => (WeqToFun w) (f x))). 
generalize Y Z w. clear Y Z w.
apply Weq_rec.  intros Y.  simpl.  exact etaExpIsWeq.
Qed.




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



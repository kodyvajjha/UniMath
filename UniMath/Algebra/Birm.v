
(** Imports **)

Require Export UniMath.Foundations.PartA.
Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.PartD.
(*The following is_a_prop given in the problem and is isaprop in UniMath. *)
Definition isProp (X:UU) : UU := ∏ (a b : X) , iscontr(paths a b).

(*The following is the same as is_a_prop' given in the problem and is isProofIrrelevant in UniMath.*)
Definition isProp'(X:UU) : UU := ∏ (a b : X), paths a b.

Print isaprop.
Print invproofirrelevance.
Print gradth.
Print proofirrelevance.
Print isapropifcontr.
Print isProofIrrelevant.
Print isaprop_isProofIrrelevant.
Print isapropifcontr.
Print isapropisaprop.


Theorem weqispropisProofIrrelevant : ∏ X:UU, isProofIrrelevant(X) ≃ isaprop(X).
  Proof.
    intros. use weqpair. (* Now we have to supply a function and a proof that it's a weq *)

    exact (invproofirrelevance X). (* This supplies the function *)

    use gradth.
    (* Now we need to supply a function going the other way and proofs that they are inverses.*)

    exact (proofirrelevance X). (* This supplies the function going the other way. *)

    (*Proof of one way inverse. *)
    intros.
    apply isapropifcontr. exists x. intros.
    unfold isProofIrrelevant in x,t.
    apply isaprop_isProofIrrelevant.

    (*Proof of the other way inverse. *)
    intros.
    apply isapropifcontr.
    exists y. intros.
    apply isapropisaprop.
Defined.

Print weqispropisProofIrrelevant.

(*
  This is the theorem which I tried to write from scratch, only to realize it would require
  a lot of intermediate lemmas to finish. I abandoned this in favor of using the previously
  proven lemmas in the UniMath library, which is what the theorem above is.
*)

Print weqispropisProofIrrelevant.
Theorem weqisprops: ∏ X:UU, isProp(X) ≃ isProp'(X).
Proof.
  intros.  use weqpair.
  unfold isProp.
  unfold isProp'.
  intros. set (ab := X0 a b).
  use iscontrpr1. exact ab.

  use gradth.

  unfold isProp'. unfold isProp.
  intros. set (pab := X0 a b).
  unfold iscontr.
  exists pab.
  intros.
  proofirrelevance.
  assert (g := fun p:(paths a b) => tpair(p, idpath p)).
 Admitted

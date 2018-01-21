(** Imports **)

Require Export UniMath.Algebra.Monoids_and_Groups.
Require Export UniMath.Algebra.Rigs_and_Rings.

(* We are trying to prove the Isomorphism theorems in UniMath. Let us start slow by proving it for groups. *)

(*

The first isomorphism theorem for groups says that if G, H are groups and  ϕ : G → H is a group homomorphism, then,
    - the kernel of φ is a normal subgroup of G
    - the image of φ is a subgroup of H
    - the quotient G/ker(φ) ≃ image of φ.

*)

Open Scope multmonoid.

Definition grkerhsubtype {G H : gr} (p : monoidfun G H) : hsubtype G :=  (λ g:G, ∥ hfiber p (unel H) ∥).
Definition grimghsubtype {G H : gr} (p : monoidfun G H) : hsubtype H :=  (λ h:H, ∃ g:G, p(g) = h ).
Parameter G : gr.
Parameter H : gr.
Parameter g : G.
Parameter p : monoidfun G H.
Parameter a : grkerhsubtype p.
Check pr2 a.


(* The kernel of a monoidfun is a subgroup *)

Lemma issubgrgrker (G H : gr) (p : monoidfun G H) : issubgr (grkerhsubtype p).
Proof.
  use issubgrpair.
  (* Now we have to prove that it is a submonoid and preserves inverses *)

  - use issubmonoidpair.
 (*Have to show it has an associative binop and identity *)
    + intros a a'.
      unfold grkerhsubtype.
      use (hinhuniv _ (pr2 a)). (* pr2 a is wit of type ∥hfiber p 1∥ *)
      intros.
      use hinhpr. exact X.
    + unfold grkerhsubtype.
      use hinhpr.
      unfold hfiber.
      exists (unel G).
      use ismonoidfununel.
      exact (pr2 p).
  (* Have to show it preserves inverses.*)
  - intros. unfold grkerhsubtype in X. unfold grkerhsubtype. exact X.
Defined.

(* The image of a monoidfun is a subgroup *)
Lemma issubgrimg (G H : gr) (p : monoidfun G H) : issubgr (grimghsubtype p).
Proof.
  use issubgrpair.
  (* Now we have to prove that it is a submonoid and that it preserves inverses *)
  - use issubmonoidpair.
    (* Have to show it has an associative binop and identity *)
    + intros a a'. unfold grimghsubtype.
      use (hinhuniv _ (pr2 a)). intros ae.
      use (hinhuniv _ (pr2 a')). intros ae'.
      set (one := pr2 ae). simpl in one.
      set (two := pr2 ae'). simpl in two.
      set (prod := pr1 ae * pr1 ae').
      use hinhpr.
      exists prod. unfold prod.
      use (pathscomp0 (binopfunisbinopfun p (pr1 ae) (pr1 ae'))).
      use two_arg_paths. exact one. exact two.
    + (* Preserves identity *)
      unfold grimghsubtype.
      use hinhpr. exists (unel G).
      exact (dirprod_pr2(pr2 p)).
  - (* Preserves inverses *)
    intros x X.
    unfold grimghsubtype in X. unfold grimghsubtype.
    use (hinhuniv _ X). intro xe.
    use hinhpr. exists (grinv G (pr1 xe)).
    unfold monoidfun in p. unfold ismonoidfun in p.
    use (pathscomp0 _ (maponpaths (λ bb : H, (grinv H bb)) (pr2 xe))).
    (* Coq now asks us to fill the hole. No pun intended. *)
    use monoidfuninvtoinv.
Defined.

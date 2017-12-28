
(** Imports **)

Require Export UniMath.Algebra.Monoids_and_Groups.
Require Export UniMath.Algebra.Rigs_and_Rings.

(*We are trying to prove the Isomorphism theorems in UniMath. Let us start slow by proving it for groups. *)

(*

The first isomorphism theorem for groups says that if G, H are groups and  ϕ : G → H is a group homomorphism, then,
    - the kernel of φ is a normal subgroup of G
    - the image of φ is a subgroup of H
    - the quotient G/ker(φ) ≃ image of φ.

*)

Open Scope multmonoid.
Parameter X : gr.
Check unel X.
Check issubgr.
Print hsubtype.

Lemma unelmonoidfun_ismonoidfun (X Y : monoid) : ismonoidfun (λ x : X, (unel Y)).
Proof.
  use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use pathsinv0. use lunax.
  - use idpath.
Qed.

Compute S 1.



Definition grkerhsubtype {G H : gr} (p : monoidfun G H) : hsubtype G :=  (λ g:G, ∥ hfiber p (unel H) ∥).
Parameter G : gr.

Print issubsetwithbinop.
Print issubgrpair.
Parameter H : gr.
Parameter p : monoidfun G H.
Check grkerhsubtype.
Check pr1.


Lemma issubgrgrker (G H : gr) (p : monoidfun G H) : issubgr (grkerhsubtype p).
Proof.
  use issubgrpair.
  - use issubmonoidpair.
    + intros a a'.
      use (hinhuniv _ (pr2 a)). intros X0.
      use (hinhuniv _ (pr2 a')). intros X1.
      use hinhpr. exact X0.
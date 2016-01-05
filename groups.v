Require Coq.Setoids.Setoid.

Module Type Sig.

  Parameter G : Type.
  Parameter e : G.

  Parameter inv : G -> G.
  Parameter mult : G -> G -> G.
  Infix "*" := mult.

  Axiom left_id : forall x : G, e * x = x.
  Axiom left_inv : forall x : G, inv x * x = e.
  Axiom assoc : forall x y z : G, x * (y * z) = (x * y) * z.

  Definition conjugate : G -> G -> G :=
    fun x y : G => inv y * x * y.

  Infix "^" := conjugate.

End Sig.

Module Group (G : Sig).
Import G.

Theorem left_cancel : forall x y z : G, x * y = x * z -> y = z.
Proof.
  intros x y z.
  intros H.
  assert (inv x * (x * y) = inv x * (x * z)) as Hinv.
    rewrite H.
    reflexivity.
  rewrite assoc in Hinv.
  rewrite assoc in Hinv.
  rewrite left_inv in Hinv.
  rewrite left_id in Hinv.
  rewrite left_id in Hinv.
  exact Hinv.
Qed.


Theorem right_id : forall x : G, x * e = x.
Proof.
  intros x.
  assert (inv x * (x * e) = inv x * x) as H.
    rewrite assoc.
    rewrite left_inv.
    apply left_id.
  apply left_cancel in H.
  exact H.
Qed.

(* Another possible proof *)
(* Proof. *)
(*   intros x. *)
(*   apply left_cancel with (x := inv x). *)
(*   rewrite assoc. *)
(*   rewrite left_inv. *)
(*   apply left_id. *)
(* Qed. *)


Theorem right_inv : forall x : G, x * inv x = e.
Proof.
  intros x.
  assert (inv x * (x * inv x) = inv x * e) as H.
    rewrite assoc.
    rewrite left_inv.
    rewrite right_id.
    apply left_id.
  apply left_cancel in H.
  exact H.
Qed.


Theorem unique_unit : forall f : G,
                        (forall x : G, f * x = x /\ x * f = x) -> e = f.
Proof.
  intros f.
  intros H.
  specialize (H e).
  elim H.
  intros Hf_is_left_unit _.
  assert (f * e = f * e) as Hunit.
    reflexivity.
  rewrite right_id in Hunit at 2.
  rewrite Hf_is_left_unit in Hunit.
  exact Hunit.
Qed.


Theorem right_unique_inv : forall x y : G, x * y = e -> inv x = y.
Proof.
  intros x y H.
  apply left_cancel with (x := x).
  rewrite H.
  apply right_inv.
Qed.


Theorem inv_is_involution : forall x : G, inv (inv x) = x.
Proof.
  intros x.
  apply right_unique_inv.
  apply left_inv.
Qed.


Theorem inv_of_mult: forall x y : G, inv (x * y) = inv y * inv x.
Proof.
  intros x y.
  apply right_unique_inv.
  rewrite <- assoc.
  rewrite assoc with (y := inv y).
  rewrite right_inv, left_id, right_inv.
  reflexivity.
Qed.


Theorem inv_of_conjugate: forall x y z : G,
    x ^ z * y ^ z = (x * y) ^ z.
Proof.
  intros x y z.
  unfold conjugate.
  rewrite assoc.
  rewrite <- assoc with (y := z).
  rewrite assoc with (x := z).
  rewrite right_inv.
  rewrite left_id.
  rewrite assoc.
  reflexivity.
Qed.

Theorem conjugate_of_unit: forall y : G, e ^ y = e.
Proof.
  intros y.
  unfold conjugate.
  rewrite right_id.
  rewrite left_inv.
  reflexivity.
Qed.

End Group.
Generalizable All Variables.

Class Group {G : Type}
            (e : G)
            (inv : G -> G)
            (dot : G -> G -> G) := {
  left_id : forall x : G, (dot e x) = x;
  left_inv : forall x : G, (dot (inv x) x) = e;
  assoc : forall x y z : G, (dot x (dot y z)) = (dot (dot x y) z)
}.

(* Infix "*" := mult : group_scope. *)

(* Open Scope group_scope. *)

Definition hom : forall A B e f invg invh dotg doth, Group e invg dotg -> Group f invh doth -> Prop :=
  hom e = f.

Theorem left_cancel `{Group G} : forall x y z : G, x * y = x * z -> y = z.
Proof.
  intros x y z.
  intros H1.
  assert (inv x * (x * y) = inv x * (x * z)) as Hinv.
    rewrite H1.
    reflexivity.
  rewrite assoc in Hinv.
  rewrite assoc in Hinv.
  rewrite left_inv in Hinv.
  rewrite left_id in Hinv.
  rewrite left_id in Hinv.
  exact Hinv.
Qed.


Theorem right_id `{Group G} : forall x : G, x * e = x.
Proof.
  intros x.
  assert (inv x * (x * e) = inv x * x) as H1.
    rewrite assoc.
    rewrite left_inv.
    apply left_id.
  apply left_cancel in H1.
  exact H1.
Qed.

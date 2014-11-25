(********************
 * DM3: Omniscience
 *
 * L'objet de ce DM est d'étudier les types qui sont omniscients dans
 * la théorie des types sous-jacente de Coq. Un type [X] est
 * omniscient quand on peut décider pour tout prédicat [X → bool] s'il
 * est vrai partout ou non.  
*)

Set Implicit Arguments.
Require Import Coq.Unicode.Utf8.
Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.

Record equivalence {X : Set} (R : X → X → Prop) : Set := 
  mkEq {
    refl: forall x, R x x;
    symm: forall x y, R x y -> R y x;
    trans: (forall x y z, R x y -> R y z -> R x z)
}.
Record setoid : Type := 
  mkSetoid {
    set : Set;
    R : set → set → Prop;
    R_eq : equivalence R
}.

Definition setoid_of_set (X : Set) : setoid.
  refine (mkSetoid (set:=X) (R := fun x y => x = y) _).
  apply mkEq; [auto | auto | apply eq_trans].
Defined.
Definition bool_setoid := setoid_of_set bool.
Definition nat_setoid := setoid_of_set nat.
Notation "'ℕ'" := (nat_setoid).

(* Question 1. *)
Definition extensional {X Y : setoid} (f : set X → set Y) :=
  forall x y, R X x y -> R Y (f x) (f y).
Hint Unfold extensional.
Definition arrow_setoid (X : setoid) (Y : setoid) : setoid.
refine (mkSetoid (set := { f : set X → set Y | extensional f })
                 (R := (fun f g => forall (x:set X), R Y ((proj1_sig f) x) ((proj1_sig g) x)))
                 _).
apply mkEq.
  intros.
  apply refl.
  apply R_eq.

  intros.
  apply symm.
    apply R_eq.

    apply H.

  intros.
    apply trans with (proj1_sig y x0).
      apply R_eq.
      auto.
      auto.
Defined.
Notation "X ⇒ Y" := (arrow_setoid X Y) (at level 80).

Definition omniscient (X : setoid) :=
  forall p : set (X ⇒ bool_setoid), 
    (exists x, proj1_sig p x = false) \/ (forall x, proj1_sig p x = true).

(* Question 2. *)
Definition searchable (X : setoid) := exists (eps:set (X ⇒ bool_setoid) -> set X), forall (p:set (X ⇒ bool_setoid)), ((proj1_sig p) (eps p)) = true -> forall x, (proj1_sig p) x = true.

(* Question 3. *)
Lemma searchable_implies_omniscient : forall X, searchable X -> omniscient X.
Proof.
  intros.
  intro.
  destruct H.
  destruct (proj1_sig p (x p)) eqn:H1.
    right.
    apply H.
    apply H1.

    left.
    exists (x p).
    apply H1.
Qed.

(* Question 4. *)
Definition finite_setoid (k: nat) : setoid.
refine (mkSetoid (set := { x | x ≤ k}) (R := (fun x y => proj1_sig x = proj1_sig y)) _).
split; [auto | auto | intros; apply eq_trans with (y := proj1_sig y); auto].
Defined.

Fixpoint epsilon_for_finite (x : nat) {k : nat} (p : set (arrow_setoid (finite_setoid k) bool_setoid)) : set (finite_setoid k) :=
  match x with
    0 => exist (fun x => x ≤ k) 0 (le_0_n k)
  | S y =>
    match (proj1_sig p (exist (fun x => x ≤ k) k (le_refl k))) with
      true => epsilon_for_finite y p
    | false => exist (fun x => x ≤ k) k (le_refl k)
  end
end.

Lemma finites_are_searchable : forall k, searchable (finite_setoid k).
Proof.
  intros.
  unfold searchable.
  exists (epsilon_for_finite k).
  induction k.
    intros.
    unfold epsilon_for_finite in H.
    intros.
    destruct x.
    destruct p.
    rewrite <-H.
    apply e.
    simpl.
    omega.

    intros.
    destruct x.
    destruct p.
    rewrite<- H.
    simpl.
Admitted.

Lemma finites_are_omniscient : forall k, omniscient (finite_setoid k).
Proof.
  intros.
  apply searchable_implies_omniscient.
  apply finites_are_searchable.
Qed.

(* Question 5. *)
Fixpoint min (f : nat → bool) (n:nat) :=
  match n with
      0 => (f 0)
    | S k => if (f (S k)) then (min f k) else false
  end.


(* Question 6. *)
Lemma if_true : forall (a:bool) (b:bool) (c:bool), (a = true) -> (if a then b else c) = b.
Proof.
  intros.
  replace a with true.
  trivial.
Qed.

Lemma if_false : forall (a:bool) (b:bool) (c:bool), (a = false) -> (if a then b else c) = c.
Proof.
  intros.
  replace a with false.
  trivial.
Qed.

Lemma no_min : forall f n, min f n = true -> (forall k, k <= n -> f k = true).
Proof.
  intros.
  induction n.
    assert (k=0).
      omega.
    rewrite H1.
    trivial.

    assert((k <= n) \/ (k = S n)).
      omega.
    assert((f (S n) = true) \/ (f (S n) = false)).
      case (f (S n)).
        auto.
        auto.
    destruct H2.
      unfold min in H.
      rewrite if_true in H.
      destruct H1.
        apply IHn.
          trivial.
          trivial.
        rewrite H1.
        trivial.
      trivial.

      exfalso.
      unfold min in H.
      rewrite if_false in H.
        apply diff_false_true.
        trivial.
        trivial.
Qed.

Lemma compute_minimum : 
  forall f n, min f n = false -> exists p, f p = false ∧ (forall k, k < p -> f k = true).
Proof.
  intros.
  induction n.
    exists 0.
    split.
      apply H.
      intros.
      omega.

    assert ((f (S n) = false)\/(f (S n) = true)).
    case (f (S n)).
      auto.
      auto.

    destruct H0.
      assert ((min f n = false)\/(min f n = true)).
      case (min f n).
        auto.
        auto.
      destruct H1.
        apply IHn.
        trivial.

        exists (S n).
        split.
          trivial.

          intros.
          apply no_min with (n:=n).
          assert((f (S n) = true) \/ (f (S n) = false)).
          case (f (S n)).
            auto.
            auto.
          destruct H3.
             unfold min.
             auto.

             unfold min.
             auto.
          omega.

        apply IHn.
        unfold min in H.
        rewrite if_true in H.
          auto.
          trivial.
Qed.

(* Question 7. *)
Definition Decreasing (α : nat -> bool) := 
  forall i k, i ≤ k -> α i = false -> α k = false.
Definition N_infty : setoid.
refine (mkSetoid 
          (set := { α : nat -> bool | Decreasing α })
          (R := fun α β => forall x, proj1_sig α x = proj1_sig β x)
          _).
apply mkEq.
  auto.

  intros.
  auto.

  intros.
  rewrite H.
  auto.
Defined.
Notation "ℕ∞" := N_infty.
Notation "x ≡ y" := (R N_infty x y) (at level 80). (* ≡ représente l'égalité sur ℕ∞ *)

(* Question 8. *)
Definition ω : set ℕ∞.
refine (exist _ (fun x => true) _).
intro.
intros.
trivial.
Defined.

(* Question 9. *)

(* comparaison entre entier renvoyant bool*)

Fixpoint gtb (a b : nat) :=
match (a, b) with
  | (0, _) => false
  | (_, 0) => true
  | (S c, S d) => gtb c d
end.

(*un lemme utile admis car pas dans l'objectif du DM*)
Lemma gtb_false : forall a b, gtb a b = false <-> a <= b.
Proof.
Admitted.

Definition of_nat (k : nat) : set ℕ∞.
  refine (exist _ (gtb k) _).
  unfold Decreasing.
  intros.
  apply gtb_false.
  apply gtb_false in H0.
  omega.
Defined.

(* Question 11. *)
Lemma LPO_equiv : omniscient ℕ <-> forall x : set ℕ∞, x ≡ ω \/ exists k, x ≡ of_nat k.
Proof.
Admitted.

(* Question 13. *)
Lemma density : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    proj1_sig p ω = true -> 
    (forall k, proj1_sig p (of_nat k) = true) -> 
    forall x, proj1_sig p x = true.
Proof.
Admitted.

(* Question 14. *)
Definition ε (p : set (ℕ∞ ⇒ bool_setoid)) : set ℕ∞.
refine (exist _ (fun n => min (fun m => proj1_sig p (of_nat m)) n) _).
Admitted.

(* Question 15. *)

Lemma ε_correct : forall p : set (ℕ∞ ⇒ bool_setoid), proj1_sig p (ε p) = true <-> forall x, proj1_sig p x = true.
Proof.
intros.
split.
  intros.
  apply density.
     unfold ω.
Admitted.

(* Question 16. *)
Theorem N_infty_omniscient : omniscient ℕ∞.
Proof.
  unfold omniscient.
  intros.
  assert (proj1_sig p (ε p) = true \/ proj1_sig p (ε p) = false).
  case (proj1_sig p (ε p)).
    left.
    trivial.

    right.
    trivial.

  destruct H.
    right.
    apply ε_correct.
    trivial.

    left.
    exists (ε p).
    trivial.
Qed.

(* Question 17. *)
Lemma finite_falsification : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    (exists x, (¬ (x ≡ ω) /\ proj1_sig p x = false)) \/ (forall n, proj1_sig p (of_nat n) = true).
Proof.
  intros.
Admitted.

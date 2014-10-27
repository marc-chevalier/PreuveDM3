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
                 (R := (fun f g => forall (x : set X), R Y (proj1_sig f x) (proj1_sig g x)))  (* to do *)
                 _).
apply mkEq.
intros f x.
apply R_eq.
intros f g H x.
apply symm.
apply R_eq.
apply H.
intros f g h H H0 x.
apply trans with (proj1_sig g x).
apply R_eq.
apply H.
apply H0.
Defined.
Notation "X ⇒ Y" := (arrow_setoid X Y) (at level 80).

Definition omniscient (X : setoid) :=
  forall p : set (X ⇒ bool_setoid), 
    (exists x, proj1_sig p x = false) \/ (forall x, proj1_sig p x = true).

(* Question 2. *)
Definition searchable (X : setoid) := 
  forall p : set (X ⇒ bool_setoid),
  exists epsilon : (set(X ⇒ bool_setoid)) -> set X,
  proj1_sig p (epsilon (p)) = true -> 
    (forall x, proj1_sig p x = true).


(* Question 3. *)
Lemma searchable_implies_omniscient : forall X, searchable X -> omniscient X.
Proof.
  intros X H p.
  

Qed.

(* Question 4. *)
Definition finite_setoid (k: nat) : setoid.
refine (mkSetoid (set := { x | x ≤ k}) (R := (fun x y => proj1_sig x = proj1_sig y)) _).
split; [auto | auto | intros; apply eq_trans with (y := proj1_sig y); auto].
Defined.

Lemma finites_are_omniscient : forall k, omniscient (finite_setoid k).
Proof.
(* to do *)
Qed.

(* Question 5. *)
Fixpoint min (f : nat → bool) (n:nat) := 
  (* to do *)

(* Question 6. *)
Lemma compute_minimum : 
  forall f n, min f n = false -> exists p, f p = false ∧ (forall k, k < p -> f k = true).
Proof.
(* to do *)
Qed.

(* Question 7. *)
Definition Decreasing (α : nat -> bool) := 
  forall i k, i ≤ k -> α i = false -> α k = false.
Definition N_infty : setoid.
refine (mkSetoid 
          (set := { α : nat -> bool | Decreasing α })
          (R := fun α β => (* to do *))
          _).
(* to do *)
Defined.
Notation "ℕ∞" := N_infty.
Notation "x ≡ y" := (R N_infty x y) (at level 80). (* ≡ représente l'égalité sur ℕ∞ *)

(* Question 8. *)
Definition ω : set ℕ∞.
refine (exist _ (fun x => true) _).
(* to do *)
Defined.

(* Question 9. *)
Definition of_nat (k : nat) : set ℕ∞.
(* to do *)
Defined.

(* Question 11. *)
Lemma LPO_equiv : omniscient ℕ <-> forall x : set ℕ∞, x ≡ ω \/ exists k, x ≡ of_nat k.
Proof.
(* to do *)
Qed.

(* Question 13. *)
Lemma density : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    proj1_sig p ω = true -> 
    (forall k, proj1_sig p (of_nat k) = true) -> 
    forall x, proj1_sig p x = true.
Proof.
(* to do *)
Qed.

(* Question 14. *)
Definition ε (p : set (ℕ∞ ⇒ bool_setoid)) : set ℕ∞.
refine (exist _ (fun n => min (fun m => proj1_sig p (of_nat m)) n) _).
(* to do *)
Defined.

(* Question 15. *)
Lemma ε_correct : forall p, p (ε p) = true <-> forall x, p x = true.
Proof.
(* to do *)
Qed.

(* Question 16. *)
Theorem N_infty_omniscient : omniscient ℕ∞.
Proof.
(* to do *)
Qed.

(* Question 17. *)
Lemma finite_falsification : 
  forall p : set (ℕ∞ ⇒ bool_setoid), 
    (exists x, (¬ (x ≡ ω) /\ proj1_sig p x = false)) \/
(forall n, proj1_sig p (of_nat n) = true).
Proof.
(* to do *)
Qed.

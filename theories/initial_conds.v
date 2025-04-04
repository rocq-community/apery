Require Import BinInt.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat.
Require Import tactics binomialz rat_of_Z seq_defs.
Require harmonic_numbers.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We state the equalities and prove evaluations of the main sequences
   a and b, to be used as initial conditions. Proofs are done by
   (internal) computation, using the field tactic so that computations
   are performed using a rather efficient binary arithmetic instead of
   type rat which is awful for 'large' scale computations.*)

(* A tactic to unroll the definition of a and preprocess the term in order *)
(* for rat_field to be able to process the equality correctly. *)
Ltac expand_a :=
(* unfolding the definition of a, c, binomials and unlocking the constant *)
(* defining the sigma, so that sums can be unrolled: *)
rewrite /a /c /binomialz unlock /=.

(* A tactic to unroll the definition of b and preprocess the term in order *)
(* for rat_field to be able to process the equality correctly. *)
Ltac expand_b :=
(* unfolding the definition of b: *)
rewrite /b; 
(* unfolding the definition of auxiliary sequence and unlocking the constant*)
(* defining the sigma, so that sums can be unrolled: *)
rewrite unlock /= /v /c /u /ghn3 /harmonic_numbers.ghn;
rewrite unlock /= /s unlock /= /d /binomialz /=;
(* normalizing the exponents (that are natural numbers) *)
rewrite ?(=^~ PoszD, addnE) /=.


(* Tactic proving an evaluation for the sequence a (fails otherwise) *)
Ltac solve_a_evaluation := by expand_a; field.

(* Tactic proving an evaluation for the sequence b (fails otherwise) *)
Ltac solve_b_evaluation := by expand_b; field.



(* Evaluations for the sequence b. With our definition we have:
        b_n = 0, 6, 351/4, 62531/36, ... *)

Lemma b0_eq : b 0 = 0.
Proof. solve_b_evaluation. Qed.

Lemma b1_eq : b 1 = 6%:Q.
Proof. solve_b_evaluation. Qed.

Lemma b2_eq : b 2 = rat_of_Z 351 / rat_of_Z 4.
Proof. solve_b_evaluation. Qed.

Lemma b3_eq : b 3 = rat_of_Z 62531 / rat_of_Z 36.
Proof. solve_b_evaluation. Qed.


(* Evaluations for the sequence b. With our definition we have:
     a_n = 1, 5, 73, 1445, 33001 ... *)

Lemma a0_eq : a 0 = 1.
Proof. solve_a_evaluation. Qed.

Lemma a1_eq : a 1 = rat_of_Z 5.
Proof. solve_a_evaluation. Qed.

Lemma a2_eq : a 2 = rat_of_Z 73.
Proof. solve_a_evaluation. Qed.

Lemma a3_eq : a 3 = rat_of_Z 1445.
Proof. solve_a_evaluation. Qed.

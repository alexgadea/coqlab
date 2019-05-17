(*begin hide*)
Require Import String. Open Scope string_scope.
Require Import Program.

From mathcomp Require Import ssreflect ssrnat ssrbool eqtype fintype.
Import ssreflect ssrnat ssrbool ssrfun eqtype fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Add LoadPath "./" as Top.
Require Import Top.CaseTactic.
Require Import Top.Syntax.
Require Import Top.Semantics.
Require Import Top.Coincidence.
Require Import Top.Substitution.

Require Import Vector.
Require Import VectorEq.
Require Import ZArith.

(*end hide*)

Definition x0 {E} := VAR (ZVAR E).
Definition x1 {E} := VAR (SVAR (ZVAR E)).
Definition x2 {E} := VAR (SVAR (SVAR (ZVAR E))).
Definition x3 {E} := VAR (SVAR (SVAR (SVAR (ZVAR E)))).

Definition Num {E} (n : nat) : IntExp E := NAT n.

Definition PLUS {E} (a b : IntExp E) : IntExp E := BNOp PlusOP a b.
Definition MINUS {E} (a b : IntExp E) : IntExp E := BNOp MinusOP a b.

Notation "'_0'" := (Num 0) (at level 1, no associativity).
Notation "'_1'" := (Num 1) (at level 1, no associativity).
Notation "'_2'" := (Num 2) (at level 1, no associativity).
Notation "'_3'" := (Num 3) (at level 1, no associativity).
Notation "'_4'" := (Num 4) (at level 1, no associativity).
Notation "'_5'" := (Num 5) (at level 1, no associativity).

Notation "− a"   := (Neg a) (at level 50, no associativity).
Notation "a + b" := (PLUS a b) (at level 50, left associativity).
Notation "a - b" := (MINUS a b) (at level 50, left associativity).

Definition TRUE  {E} : Assert E := BOOL true.
Definition FALSE {E} : Assert E := BOOL false.

Definition AND {E} (a b : Assert E) : Assert E := BBOp AndOP a b.
Definition OR {E} (a b : Assert E) : Assert E := BBOp OrOP a b.

Notation "¬ a" := (Not a) (at level 50, left associativity).
Notation "a ∧ b" := (AND a b) (at level 50, left associativity).
Notation "a ∨ b" := (OR a b) (at level 50, left associativity).

Definition EQ {E} (a b : IntExp E) : Assert E := OOp EqOP a b.
Definition LE {E} (a b : IntExp E) : Assert E := OOp LeOP a b.

Notation "a ⩵ b" := (EQ a b) (at level 50, left associativity).
Notation "a ≤ b"  := (LE a b) (at level 50, left associativity).

Definition FA {E} (a : Assert E.+1) : Assert E := Quant ForallOP a.
Definition EX {E} (a : Assert E.+1) : Assert E := Quant ExistOP a.

Notation "∀ a" := (FA a) (at level 50, left associativity).
Notation "∃ a" := (EX a) (at level 50, left associativity).

Eval compute in ⟦ _1 + _2 ⟧ᵢ [ ].
Eval compute in ⟦ _1 + _1 + (_2 - _5)  ⟧ᵢ [ ].
Eval compute in ⟦ _1 + _1 + (− _2 - _5)  ⟧ᵢ [ ].

Eval compute in ⟦ _1 + _1 + (x0 - _5)  ⟧ᵢ [ 10%Z ].
Eval compute in ⟦ x2 - x1  ⟧ᵢ [ 10%Z , 15%Z , 30%Z ].
Eval compute in ⟦ _1 + _1 + (x0 + x1) - x2  ⟧ᵢ [ 10%Z , 15%Z , 30%Z ].

Eval compute in ⟦ (x1 + x0) ⩵ (x0 + x1)  ⟧ₐ [ 10%Z , 15%Z ].

Definition x01 := @x0 1.
Definition x10 := @x1 0.

Definition eval_prop :=
  Eval compute in ⟦ ∀ (∀ ((x10 + x01) ⩵ (x01 + x10)) ) ⟧ₐ [ ].

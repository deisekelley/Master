(**************************** Exercise: 1 star  (nandb)  *********************)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true  => match b2 with
             | false => true
             | true  => false
             end
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

(************************** Exercise: 1 star (andb3) ***************************)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
   match b1 with
   | false => false
   | true  => match b2 with
              | false => false
              | true  => b3
              end
   end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


(************************** Exercise: 1 star (factorial) ***************************)

Fixpoint plus (n : nat) (m : nat) : nat :=
	match n with
		| 0 => m
		| S n' => S (plus n' m)
	end.


Fixpoint mult (n m : nat) : nat :=
	match n with
		| 0 => 0
		| S n' => plus m (mult n' m)
	end.

Fixpoint factorial (n:nat) : nat :=
    match n with
    | 0 => 1
    | S n' => mult n (factorial n')
    end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


(**************************  Exercise: 1 star (blt_nat) ***************************)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.


Definition blt_nat (n m : nat) : bool := 
                    (andb (negb (beq_nat n m)) (leb n m)).


Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


(************************** Exercise: 1 star (plus_id_exercise) ***************************)

Theorem plus_id_exercise : forall n m o : nat,
  n = m ->  m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros Ha.
  intros Hb.
  rewrite -> Ha.
  rewrite <- Hb.
  reflexivity. Qed.

(************************** Exercise: 2 stars (mult_S_1) ***************************)


Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intro Ha.
  rewrite -> Ha.
  reflexivity.
Qed.

(************************** Exercise: 2 stars (andb_true_elim2) ***************************)


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
   - simpl in H. assumption.
   - simpl in H.
   congruence.
(************************** Exercise: 1 star (zero_nbeq_plus_1) ***************************)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'].
   - reflexivity.
   - reflexivity.
Qed.


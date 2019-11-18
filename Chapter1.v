From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.

Module Chapter1.

Definition g1 (n : nat) (m : nat) : nat := n + m * 2.

(* Contiguous arguments of one and the same type can be grouped *)
Definition g2 (n m : nat) : nat := n + m * 2.

Definition g3 (n : nat) : nat -> nat := fun m => n + m * 2.

(* These 3 functions are the same *)
About g1.
About g2.
About g3.

Eval compute in g1 2 3.
Eval hnf in g1 2 3.
Eval cbv in g1 2 3.

Definition repeat_twice (g : nat -> nat) : nat -> nat :=
  fun x => g (g x).

Eval compute in repeat_twice S 0.

Definition pred5 n :=
  if n is u.+1.+1.+1.+1.+1 then u else 0.

Eval compute in (pred5 6).
Eval compute in (pred5 4).

Definition three_patterns n :=
  match n with
  | u.+1.+1.+1.+1.+1 => u
  | v.+1 => v
  | 0 => n
  end.

Eval compute in (three_patterns 3).
Eval compute in (three_patterns 6).

Fixpoint addn n m :=
  if n is p.+1 then (addn p m).+1 else m.

(* Различные нотации для n-арных операций *)

(* Для добавления нескольких голов к существующему списку *)
Compute [:: 1, 2 & [:: 3; 4]].

Compute [&& true, false & true].
Compute [|| false, false | true].

(* Сompute -- синоним для [Eval vm_compute in]
   (редукция делается в виртуальной машине) *)

Definition head T (x0 : T) (s : seq T)  :=
  if s is x :: _ then x else x0.

Compute (head 0 nil).
Compute (@head _ 0 [:: 1; 2]).
Compute (@head nat 0 [:: 3; 4]).

Fixpoint size A (s : seq A) :=
  if s is _ :: tl then (size tl).+1 else 0.

Fixpoint map A B (f : A -> B) s :=
  if s is e :: tl then f e :: map f tl else nil.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s).

Compute [seq i.+1 | i <- [:: 2; 3]].
Compute [seq i <- [:: 1; 2; 3] | ~~odd i].

Inductive option A :=
| None
| Some (a : A).

(* Это сделает аргумент неявным и максимально вставленным,
   что значит, что даже ни к чему не примененный терм
   [None] на самом деле эквивалентен [@None _] *)
Arguments None {A}.

Definition only_odd (n : nat) : option nat :=
  if odd n then Some n else None.

Definition ohead (A : Type) (s : seq A) :=
  if s is x :: _ then Some x else None.

Inductive pair (A B : Type) : Type := mk_pair (a : B) (b : B).

Notation "( a , b )" := (mk_pair a b).
Notation "A * B" := (pair A B).

(* Notation scope delimiters: *)

Compute (5 * 2)%nat.
Compute (nat * bool)%type.

(* Records *)

Record point1 : Type :=
  Point1 { x : nat; y : nat; z : nat }.

(* Notice that the following projections are
   automatically generated for us:
   - x is defined
   - y is defined
   - z is defined *)

Compute x (Point1 3 0 2).
Compute y (Point1 3 0 2).
Compute z (Point1 3 0 2).

(* But the definition above is basically the same as: *)

Inductive point2 : Type :=
  Point (x : nat) (y : nat) (z : nat).

(* The projection is defined like so: *)

Definition x' (p : point2) :=
  match p with Point a _ _ => a end.

(* Specifal syntax for irrefutable patterns
   (when there is only a single constructor): *)

Definition x'' (p : point2) :=
  let: Point a _ _ := p in a.

(* Если нескольким ф-циям нужно работать с некоторыми общими данными,
   то существует возможность задать некоторое общее окружение при
   помощи механизма секций [Section] и переменных [Variable(s)] *)

Section iterators.
  (* Секционные переменные *)
  Variables (T : Type) (A : Type).
  Variables (f : T -> A -> A).

  (* Для всех имён [x] используй тип [T] *)
  Implicit Type x : T.

  Fixpoint iter n op x :=
    if n is p.+1 then op (iter p op x) else x.

  Fixpoint foldr a s :=
    if s is y :: ys then f y (foldr a ys) else a.

  (* Пока что [foldr] ещё не полиморфный:
     [A -> seq T -> A] *)
  About foldr.

  Variable init : A.
  Variables x1 x2 : T.

  Compute foldr init [:: x1; x2].
  (* В данном слечае Coq вычислит значение
     этого выражения символически:

     [f x1 (f x2 init)] *)

  (* Когда мы закрываем секцию, то все секционные переменные
     становятся явными параметрами, а переменные, которые
     так и не были использованы -- стираются *)
End iterators.

About iter.
About foldr.

Compute iter 5 predn 7.
Compute foldr addn 0 [:: 1; 2].

(* [iota] is a natural numbers generator:
   [:: m; m+1; ...; m+n-1] *)

Fixpoint iota m n :=
  if n is u.+1
  then m :: iota m.+1 u
  else [::].

(* Sigma-notation: *)
Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i acc => F + acc)
         0 (* initial value *)
         (iota m (n - m))). (* iota-generated sequence *)

Compute \sum_ (1 <= i < 5) (i * 2 - 1).
(*             ^- m  n -^    ^ F ^ *)
Compute \sum_ (1 <= i < 5) i.
(*                      F -^ *)


Fixpoint all_words (T : Type) (n : nat) (xs : seq T) :=
  if n is m.+1 then
    flatten [seq [seq x :: w | w <- (all_words m xs)] | x <- xs]
  else
    [:: nil; nil].

Compute (all_words 2 [:: 1; 2; 3]).

(*  [:: [:: 1; 1]; [:: 1; 2]; [:: 1; 3];
        [:: 2; 1]; [:: 2; 2]; [:: 2; 3];
        [:: 3; 1]; [:: 3; 2]; [:: 3; 3]
    ] *)
End Chapter1.

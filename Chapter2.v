From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.

Module Chapter2.

  (* Большинство из этого я уже знаю,
     поэтому буду много пропускать. *)

  Lemma muln_eq0 m n :
    (m * n == 0) = (m == 0) || (n == 0).
  Proof.
    (* Читается как: [m] может быть или [0] или
       некоторым выражением [m.+1] (для нового [m])*)
    case: m=> [|m].
    by [].
    (* По умолчанию successor case становится 2-ой подцелью
       (согласно порядку, в котором определены конструкторы
       соответствующего индуктивного типа). Мы можем это изменить
       при помощи [; last first] "суффикса" *)
    case: n=> [|k]; last first.
    - by [].
    by rewrite muln0.
  Abort.

  Lemma seq_eq_ext (s1 s2 : seq nat) :
    size s1 = size s2 ->
    (forall i : nat, nth 0 s1 i = nth 0 s2 i) ->
    s1 = s2.
  Proof.
  Admitted.

  Lemma size_map (T1 T2 : Type) :
    forall (f : T1 -> T2) (s : seq T1),
      size (map f s) = size s.

    (* [forall (f : T1 -> T2) (s : seq T1)]
       is a syntactic sugar for
       [forall f : T1 - T2, forall s : seq T1] *)
  Admitted.

  (* Квантификаторы так же могут быть
     использованы в теле определений *)
  Definition commutative (S T : Type) (op : S -> S -> T) :=
    forall x y, op x y = op y x.

  (* Такие определения позволяют более лаконично
     записывать вещи вроде *)
  Lemma addnC : commutative addn. Admitted.

  Check (3 = 3).
  Check (commutative addn).

  Lemma leqnn n : n <= n. Proof. Admitted.

  Lemma example1 a b : a + b <= a + b.
  Proof. apply: leqnn. Qed.

  (* The comparison performed by the
     [apply] tactic is up to computation *)
  (* Т.е. перед тем, как применить тактику [apply] с указанной леммой,
     будут выполнены возможные символические вычисления *)
  Lemma example2 a b : a.+1 + b <= (a + b).+1.
  Proof. apply: leqnn. Qed.

  (* Чтобы упростить доказательства, мы можем усилить терминатор [by],
     включив в него некоторые дополнительные леммы.
     Для этого используется команда [Hint Resolve]: *)
  Hint Resolve leqnn. (* Это нужно писать рядом с доказанной леммой *)

  (* Теперь предыдущую лемму можно доказать тривиально *)
  Lemma example3 a b : a + b <= a + b.
  Proof. by []. Qed.

  Lemma contra' (c b : bool) : (c -> b) -> ~~ b -> ~~ c.
  Proof.
    (* rewrite /negb. *)
    case: b.
    - by [].
    case: c.
    - by [].
    by [].
  Qed.

  Lemma negbNE' b : ~~ ~~ b -> b.
  Proof.
    rewrite /negb.
    case: b.
    - by [].
    by [].
  Qed.

  Locate "%|".
  About dvdn.
  (* Definition dvdn d m := m %% d == 0. *)

  Lemma prime_example1 m p :
    (* - [p] простое
       - [p] делит [m! + 1] без остатка *)
    prime p -> p %| m`! + 1 -> m < p.
  Proof.
    move=> H_prime_p.
    (* Преoбразуем в обратное утверждение *)
    (* contraLR : forall c b : bool,
       (~~ c -> ~~ b) -> b -> c *)
    apply: contraLR.

    (* leqNgt : forall m n : nat,
       (m <= n) = ~~ (n < m) *)
    rewrite -leqNgt=> leq_p_m.
    (* dvdn_addr : forall m d n : nat,
       d %| m -> (d %| m + n) = (d %| n) *)

    (* Можно переписывать и "условные равенства".
       При попытке это сделать нам придётся доказать предпосылку
       (создастся\добавится соответствующая подцель). *)
    rewrite dvdn_addr.

    (* gtnNdvd n d : 0 < n -> n < d -> (d %| n) = false *)
    rewrite gtnNdvd=> // //.
    (* Сразу убрали 2 тривиально-доказуемых неравенства при помощи [// //]. *)
    - apply: prime_gt1. (* prime_gt1 p : prime p -> 1 < p *)
      exact: H_prime_p.
   (* dvdn_fact m n : 0 < m <= n -> m %| n`! *)
   apply: dvdn_fact.
   (* Имеем [0 < p <= m], что есть сокращённая запись для
      [(0 < p) && (p <= m)] *)
   (* Воспользуемся [prime_gt0 p : prime p -> 0 < p].
      Нужно это читать как [prime p -> 0 < p = true] *)
   (* Тут происходит по сути тоже самое, что и в примере выше, где
      мы переписывали с [dvdn_addr] -- Coq заменит [0 < p] на [true] и
      попросит нас доказать препосылку [prime p] *)
   rewrite prime_gt0.
   - exact: leq_p_m.
   - exact: H_prime_p.
  Qed.

End Chapter2.

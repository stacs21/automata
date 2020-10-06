theory Sufficient
  imports Computation
begin

datatype ('s, 'b) tdfa_s = STATE "('b list \<times> ('s \<times> nat) set)" | REJECT

context bNFT
begin

definition "K' \<equiv> K + output_speed"

definition tdfa_init :: "('s, 'b) tdfa_s" where
  "tdfa_init = (if active init [] then STATE ([], {(init, 0)}) else REJECT)"

definition tdfa_accept :: "('s, 'b) tdfa_s \<Rightarrow> bool" where
  "tdfa_accept q \<longleftrightarrow> (case q of STATE (bs, qs) \<Rightarrow> (\<exists>(q, n) \<in> qs. accept q \<and> n = length bs)
  | _ \<Rightarrow> False)"

definition tdfa_Q :: "('s, 'b) tdfa_s set" where
  "tdfa_Q = {REJECT} \<union> STATE ` ({(bs :: 'b list, qs). length bs \<le> K' \<and>
    qs \<subseteq> {(q, n). q \<in> Q \<and> n \<le> length bs}})"

definition upd_qs :: "'a \<Rightarrow> 'b list \<Rightarrow> ('s \<times> nat) set \<Rightarrow> ('s \<times> nat) set" where
  "upd_qs a bs qs = (\<Union>((\<lambda>(q, n). {(q', n'). active q' (drop n' bs) \<and> n \<le> n' \<and> n' \<le> length bs \<and>
    \<delta> q a (q', take (n' - n) (drop n bs))}) ` qs))"

definition drop_qs :: "nat \<Rightarrow> ('s \<times> nat) set \<Rightarrow> ('s \<times> nat) set" where
  "drop_qs m qs = {(q, n). (q, n + m) \<in> qs}"

definition ext_qs :: "'b \<Rightarrow> 'b list \<Rightarrow> ('s \<times> nat) set \<Rightarrow> ('s \<times> nat) set" where
  "ext_qs b bs qs = {(q, n) \<in> qs. active q (drop n (bs @ [b]))}"

fun tdfa_step :: "('s, 'b) tdfa_s \<Rightarrow> ('a Al \<times> 'b Al) \<Rightarrow>
  (('s, 'b) tdfa_s \<times> bool \<times> bool) option" where
  "tdfa_step (STATE (bs, qs)) (Symb a, Symb b) = (if length bs < K' then
    (let qs' = ext_qs b bs qs; m = Min (snd ` qs') in
    if qs' \<noteq> {} then Some (STATE (drop m (bs @ [b]), drop_qs m qs'), False, True) else None)
  else
    (let qs' = upd_qs a bs qs; m = Min (snd ` qs') in
    if qs' \<noteq> {} then Some (STATE (drop m bs, drop_qs m qs'), True, False) else None))"
| "tdfa_step (STATE (bs, qs)) (Symb a, Blank) =
  (let qs' = upd_qs a bs qs; m = Min (snd ` qs') in
    if qs' \<noteq> {} then Some (STATE (drop m bs, drop_qs m qs'), True, False) else None)"
| "tdfa_step _ _ = None"

lemma upd_qs_tdfa_Q: "STATE (bs, qs) \<in> tdfa_Q \<Longrightarrow> STATE (bs, upd_qs a bs qs) \<in> tdfa_Q"
  using \<delta>_closed
  by (force simp add: upd_qs_def tdfa_Q_def)

lemma drop_qs_tdfa_Q: "STATE (bs, qs) \<in> tdfa_Q \<Longrightarrow> qs \<noteq> {} \<Longrightarrow> m = Min (snd ` qs) \<Longrightarrow>
  STATE (drop m bs, drop_qs m qs) \<in> tdfa_Q"
  by (force simp add: drop_qs_def tdfa_Q_def)

lemma ext_qs_tdfa_Q: "STATE (bs, qs) \<in> tdfa_Q \<Longrightarrow> length bs < K' \<Longrightarrow>
  STATE (bs @ [b], ext_qs b bs qs) \<in> tdfa_Q"
  by (force simp add: ext_qs_def tdfa_Q_def)

lemma init_in_tdfa_Q: "tdfa_init \<in> tdfa_Q"
  using init_in_Q
  by (auto simp add: tdfa_init_def tdfa_Q_def)

lemma finite_tdfa_Q: "finite tdfa_Q"
proof -
  have "tdfa_Q \<subseteq> {ACCEPT, REJECT} \<union>
    STATE ` ({bs :: 'b list. length bs \<le> K'} \<times> {qs. qs \<subseteq> Q \<times> {0..K'}})"
    using tdfa_Q_def by fastforce
  moreover have "finite ({bs :: 'b list. length bs \<le> K'} \<times> {qs. qs \<subseteq> Q \<times> {0..K'}})"
    using finite_bounded_lists finite_Q by auto
  ultimately show ?thesis
    using finite_subset by auto
qed

lemma tdfa_closed: "q \<in> tdfa_Q \<Longrightarrow> tdfa_step q ab = Some (q', b1, b2) \<Longrightarrow> q' \<in> tdfa_Q"
  apply (induction q ab rule: tdfa_step.induct)
  using drop_qs_tdfa_Q[OF ext_qs_tdfa_Q] drop_qs_tdfa_Q[OF upd_qs_tdfa_Q]
  by (fastforce simp: Let_def split: if_splits)+

interpretation tdfa: oTDFA tdfa_init tdfa_step tdfa_accept tdfa_Q
  apply standard
  using tdfa_closed
        apply (auto simp add: tdfa_accept_def finite_tdfa_Q init_in_tdfa_Q)[3]
  subgoal for q a b q' b2
    by (induction q "(a, b)" rule: tdfa_step.induct) (auto split: if_splits)
  subgoal for q a b q' b1
    by (induction q "(a, b)" rule: tdfa_step.induct) (auto simp: Let_def split: if_splits)
  subgoal for q a b q'
    by (induction q "(a, b)" rule: tdfa_step.induct) (auto simp: Let_def split: if_splits)
  subgoal for q a b q'
    by (induction q "(a, b)" rule: tdfa_step.induct) (auto simp: Let_def split: if_splits)
  done

lemmas tdfa_axioms = tdfa.TDFA_axioms

lemma finite_tdfa_Q_qs: "STATE (bs, qs) \<in> tdfa_Q \<Longrightarrow> finite qs"
proof -
  assume assms: "STATE (bs, qs) \<in> tdfa_Q"
  then have "qs \<subseteq> Q \<times> {0..length bs}"
    using tdfa_Q_def by auto
  then show "finite qs"
    using finite_Q finite_subset by auto
qed

definition tdfa_inv :: "'a list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b Al \<Rightarrow> ('s \<times> nat) set \<Rightarrow> bool" where
  "tdfa_inv as' bs' bs b qs \<longleftrightarrow> (\<forall>(q, n) \<in> qs. q \<in> Q \<and> n \<le> length bs) \<and>
    (\<forall>q n. n \<le> length bs' \<and> init \<leadsto>(as', take n bs') q \<and> active q (drop n bs' @ bs) \<longrightarrow>
      n = length bs') \<and>
    (case b of Blank \<Rightarrow> True | Symb b' \<Rightarrow>
      (\<forall>q b'' bs''. \<not>(init \<leadsto>(as', bs' @ bs @ b'' # bs'') q \<and> active q []))) \<and>
    (\<forall>q n. q \<in> Q \<and> n \<le> length bs \<longrightarrow> ((q, n) \<in> qs \<longleftrightarrow>
      init \<leadsto>(as', bs' @ take n bs) q \<and> active q (drop n bs)))"

definition tdfa_inv_aligned :: "'a list \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> 'b Al \<Rightarrow>
  ('s \<times> nat) set \<Rightarrow> bool" where
  "tdfa_inv_aligned as' bs' bs b qs \<longleftrightarrow> (\<exists>qm. (qm, 0) \<in> qs) \<and> tdfa_inv as' bs' bs b qs"

lemma tdfa_inv_init: "active init [] \<Longrightarrow>
  tdfa_inv_aligned [] [] [] (safe_hd bs'') {(init, 0)}"
  using init_in_Q no_step
  by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def split: Al.splits list.splits)

lemma app_eq_app: "cs @ cs' = bs' @ bs @ bs'' \<Longrightarrow> length bs' \<le> length cs \<Longrightarrow>
  \<exists>ds ds'. cs = bs' @ ds \<and> bs @ bs'' = ds @ ds'"
  apply (induction bs' arbitrary: cs cs' bs bs'')
   apply (metis self_append_conv2)
  by (metis (full_types) append_eq_append_conv_if append_eq_conv_conj)

lemma app_eq_app': "bs @ b'' # bs'' = ds @ ds' \<Longrightarrow> length bs < length ds \<Longrightarrow>
  \<exists>e es. ds = bs @ e # es"
  by (metis append_eq_append_conv_if id_take_nth_drop leD)

lemma tdfa_inv_upd_qs: "tdfa_inv_aligned as' bs' bs b qs \<Longrightarrow>
  (case b of Blank \<Rightarrow> True | Symb b' \<Rightarrow> length bs \<ge> K') \<Longrightarrow>
  tdfa_inv (as' @ [a]) bs' bs b (upd_qs a bs qs)"
proof -
  assume assms: "tdfa_inv_aligned as' bs' bs b qs"
    "(case b of Blank \<Rightarrow> True | Symb b' \<Rightarrow> length bs \<ge> K')"
  have assms': "\<And>q n. n \<le> length bs' \<Longrightarrow> init \<leadsto>(as', take n bs') q \<Longrightarrow>
    active q (drop n bs' @ bs) \<Longrightarrow> n = length bs'"
    using assms(1) unfolding tdfa_inv_aligned_def tdfa_inv_def by fast
  obtain qm where qm_def: "(qm, 0) \<in> qs" "qm \<in> Q" "init \<leadsto>(as', bs') qm" "active qm bs"
    using assms(1) by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
  define qs' where "qs' = upd_qs a bs qs"
  have qs_dest: "\<And>q n. (q, n) \<in> qs \<Longrightarrow>
    q \<in> Q \<and> n \<le> length bs \<and> init \<leadsto>(as', bs' @ take n bs) q \<and> active q (drop n bs)"
    using assms(1) by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
  have qs'_dest: "\<And>q n. (q, n) \<in> qs' \<Longrightarrow>
    q \<in> Q \<and> n \<le> length bs \<and> init \<leadsto>(as' @ [a], bs' @ take n bs) q \<and> active q (drop n bs)"
  proof -
    fix q' n'
    assume lassm: "(q', n') \<in> qs'"
    then obtain q n where qn_def: "(q, n) \<in> qs" "active q' (drop n' bs)" "n \<le> n'"
      "n' \<le> length bs" "\<delta> q a (q', take (n' - n) (drop n bs))"
      by (auto simp add: qs'_def upd_qs_def)
    have q'_Q: "q' \<in> Q"
      using qs_dest[OF qn_def(1)] qn_def(5) \<delta>_closed by auto
    have "init \<leadsto>(as', bs' @ take n bs) q"
      using qs_dest[OF qn_def(1)] by auto
    then have "init \<leadsto>(as' @ [a], bs' @ take n' bs) q'"
      using qn_def(3,4,5) computation_snoc[OF _ qn_def(5)]
      by (metis (no_types, lifting) append_eq_appendI le_add_diff_inverse take_add)
    then show "q' \<in> Q \<and> n' \<le> length bs \<and> init \<leadsto>(as' @ [a], bs' @ take n' bs) q' \<and>
      active q' (drop n' bs)"
      using q'_Q qn_def(2,4) by auto
  qed
  have qs_intro: "\<And>q n. q \<in> Q \<Longrightarrow> n \<le> length bs \<Longrightarrow> init \<leadsto>(as', bs' @ take n bs) q \<Longrightarrow>
    active q (drop n bs) \<Longrightarrow> (q, n) \<in> qs"
    using assms(1) by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
  have qs'_intro: "\<And>q n. q \<in> Q \<Longrightarrow> n \<le> length bs \<Longrightarrow> init \<leadsto>(as' @ [a], bs' @ take n bs) q \<Longrightarrow>
    active q (drop n bs) \<Longrightarrow> (q, n) \<in> qs'"
  proof -
    fix q' n'
    assume lassms: "q' \<in> Q" "n' \<le> length bs" "init \<leadsto>(as' @ [a], bs' @ take n' bs) q'"
      "active q' (drop n' bs)"
    obtain q'' cs cs' where split: "init\<leadsto>(as', cs) q''" "\<delta> q'' a (q', cs')" "q'' \<leadsto>([a], cs') q'"
      "bs' @ take n' bs = cs @ cs'"
      using computation_split[OF lassms(3)] step_dest by fastforce
    have active_q'': "active q'' (cs' @ drop n' bs)"
      using active_comp lassms(4) split(3) by auto
    have "length cs \<ge> length bs'"
      using split(1,4) assms' active_q'' lassms(2)
      apply (auto simp add: append_eq_append_conv_if split: if_splits)
      by (metis nat_le_linear)
    then obtain n where n_def: "cs = bs' @ take n bs" "n \<le> n'"
      using split(4) lassms(2)
      apply (auto simp add: append_eq_append_conv_if append_eq_conv_conj)
      by (metis append_eq_conv_conj min.cobounded1 min.commute take_take)
    have cs'_drop: "cs' @ drop n' bs = drop n bs"
      using split(4)[unfolded n_def(1)] n_def(2)
      by (metis append.assoc append_take_drop_id same_append_eq)
    have cs'_take: "cs' = take (n' - n) (drop n bs)"
      using split(4)[unfolded n_def(1)] n_def(2)
      by (metis append.assoc le_add_diff_inverse same_append_eq take_add)
    have q''_Q: "q'' \<in> Q"
      using split(1) init_in_Q comp_closed by auto
    have q''_n_qs: "(q'', n) \<in> qs"
      using qs_intro q''_Q n_def(2) lassms(2) split(1) active_q''
      by (auto simp add: n_def(1) cs'_drop)
    then show "(q', n') \<in> qs'"
      using n_def(2) lassms(2) active_q'' split(2) lassms(4)
      by (auto simp add: qs'_def upd_qs_def cs'_take)
  qed
  have "\<And>q n. n \<le> length bs' \<Longrightarrow> init \<leadsto>(as' @ [a], take n bs') q \<Longrightarrow>
    active q (drop n bs' @ bs) \<Longrightarrow> n = length bs'"
  proof -
    fix q n'
    assume lassms: "n' \<le> length bs'" "init \<leadsto>(as' @ [a], take n' bs') q"
      "active q (drop n' bs' @ bs)"
    obtain q'' cs cs' where split: "init \<leadsto>(as', cs) q''" "q'' \<leadsto>([a], cs') q"
      "take n' bs' = cs @ cs'"
      using computation_split[OF lassms(2)] by auto
    obtain n where n_def: "cs = take n bs'" "n \<le> n'"
      using split(3) lassms(1)
      by (metis append_eq_conv_conj min.cobounded1 min.commute take_take)
    have "drop n bs' = cs' @ drop n' bs'"
      using n_def lassms(1) split(3)
      by (metis append.assoc append_take_drop_id same_append_eq)
    then have "active q'' (drop n bs' @ bs)"
      using active_comp[OF lassms(3) split(2)] by auto
    then show "n' = length bs'"
      using assms'[OF _ split(1)[unfolded n_def(1)]] n_def(2) lassms(1) by auto
  qed
  moreover have "(case b of Blank \<Rightarrow> True | Symb b' \<Rightarrow>
    (\<forall>q b'' bs''. \<not>(init \<leadsto>(as' @ [a], bs' @ bs @ b'' # bs'') q \<and> active q [])))"
  proof (cases b)
    case (Symb b')
    have len_bs: "length bs \<ge> K + output_speed"
      using assms(2)[unfolded Symb] by (auto simp add: K'_def)
    have "\<And>q b'' bs''. \<not> (init\<leadsto>(as' @ [a], bs' @ bs @ b'' # bs'')q \<and> active q [])"
    proof (rule ccontr)
      fix q b'' bs''
      assume lassm: "\<not> \<not> (init\<leadsto>(as' @ [a], bs' @ bs @ b'' # bs'')q \<and> active q [])"
      then obtain q'' cs cs' where split: "init \<leadsto>(as', cs) q''" "q'' \<leadsto>([a], cs') q"
        "cs @ cs' = bs' @ bs @ b'' # bs''"
        using computation_split by fastforce
      then have "\<delta> q'' a (q, cs')"
        using step_dest by auto
      then have "length cs' \<le> output_speed"
        using init_in_Q comp_closed[OF split(1)] output_speed_step by auto
      moreover have "length cs + length cs' \<ge> length bs' + K + output_speed + 1"
        using arg_cong[OF split(3), of length] len_bs by auto
      ultimately have len_cs: "length cs \<ge> length bs' + K + 1"
        by auto
      then obtain ds ds' where split': "cs = bs' @ ds" "bs @ b'' # bs'' = ds @ ds'"
        using app_eq_app[OF split(3)] by auto
      have active_q'': "active q'' []"
        using lassm active_comp split(2) active_mono by blast
      show "False"
      proof (cases "length ds \<le> length bs")
        case True
        have "active qm ds"
          using qm_def(4) split'(2) True active_mono[of qm ds]
          by (metis app_eq_app append.left_neutral)
        then have "length ds \<le> K"
          using bounded'[OF split(1)[unfolded split'] active_q'' qm_def(3)] by auto
        then show ?thesis
          using arg_cong[OF split'(1), of length, simplified] len_cs by auto
      next
        case False
        obtain e es where es_def: "ds = bs @ e # es"
          using app_eq_app'[OF split'(2)] False by auto
        have "(\<forall>q b'' bs''. \<not>(init \<leadsto>(as', bs' @ bs @ b'' # bs'') q \<and> active q []))"
          using assms(1) Symb by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
        then show ?thesis
          using split(1)[unfolded split'(1) es_def] active_q'' by auto
      qed
    qed
    then show ?thesis
      unfolding Symb
      by auto
  qed auto
  ultimately show "tdfa_inv (as' @ [a]) bs' bs b (upd_qs a bs qs)"
    unfolding qs'_def[symmetric] tdfa_inv_def
    using qs'_dest qs'_intro by fast
qed

lemma drop_take_drop: "n \<le> m \<Longrightarrow> m \<le> length bs \<Longrightarrow> drop n bs = drop n (take m bs) @ drop m bs"
  by (metis append.assoc append_eq_conv_conj append_take_drop_id length_take min.absorb2)

lemma tdfa_inv_drop_qs: "tdfa_inv as' bs' bs b qs \<Longrightarrow> qs \<noteq> {} \<Longrightarrow> m = Min (snd ` qs) \<Longrightarrow>
  m \<le> length bs \<and> tdfa_inv_aligned as' (bs' @ take m bs) (drop m bs) b (drop_qs m qs)"
proof -
  assume assms: "tdfa_inv as' bs' bs b qs" "qs \<noteq> {}" "m = Min (snd ` qs)"
  define qs' where "qs' = drop_qs m qs"
  have qs_dest: "\<And>q n. (q, n) \<in> qs \<Longrightarrow>
    q \<in> Q \<and> n \<le> length bs \<and> init \<leadsto>(as', bs' @ take n bs) q \<and> active q (drop n bs)"
    using assms(1) by (auto simp add: tdfa_inv_def)
  have qs_sub: "qs \<subseteq> Q \<times> {0..length bs}"
    using assms(1) by (auto simp add: tdfa_inv_def)
  then have snd_qs: "finite (snd ` qs)" "snd ` qs \<noteq> {}"
    using finite_Q finite_subset assms(2) by fastforce+
  have m_leq_bs: "m \<le> length bs"
    using assms(3) qs_dest Min_in[OF snd_qs] by auto
  obtain qm where qm_def: "(qm, m) \<in> qs"
    using Min_in[OF snd_qs] by (auto simp add: assms(3))
  then have qm_zero: "(qm, 0) \<in> qs'"
    by (auto simp add: qs'_def assms(3) drop_qs_def)
  have min: "\<And>q n. n \<le> length bs' \<Longrightarrow> init \<leadsto>(as', take n bs') q \<Longrightarrow>
    active q (drop n bs' @ bs) \<Longrightarrow> n = length bs'"
    using assms(1) by (auto simp add: tdfa_inv_def)
  have qs_intro: "\<And>q n. q \<in> Q \<Longrightarrow> n \<le> length bs \<Longrightarrow> init \<leadsto>(as', bs' @ take n bs) q \<Longrightarrow>
    active q (drop n bs) \<Longrightarrow> (q, n) \<in> qs"
    using assms(1) by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
  have "\<And>q n. n \<le> length (bs' @ take m bs) \<Longrightarrow> init \<leadsto>(as', take n (bs' @ take m bs)) q \<Longrightarrow>
    active q (drop n (bs' @ take m bs) @ (drop m bs)) \<Longrightarrow> n = length (bs' @ take m bs)"
  proof -
    fix q n
    assume lassms: "n \<le> length (bs' @ take m bs)" "init \<leadsto>(as', take n (bs' @ take m bs)) q"
      "active q (drop n (bs' @ take m bs) @ (drop m bs))"
    show "n = length (bs' @ take m bs)"
    proof (cases "n \<ge> length bs'")
      case True
      have q_Q: "q \<in> Q"
        using init_in_Q comp_closed lassms(2) by auto
      define n' where "n' = n - length bs'"
      have n'_le_bs: "n' \<le> length bs"
        using True lassms(1) m_leq_bs
        by (simp add: n'_def)
      have "init \<leadsto>(as', bs' @ take n' bs) q"
        using lassms(1,2) True m_leq_bs
        by (auto simp add: min_absorb1 n'_def)
      moreover have "active q (drop n' bs)"
      proof -
        have "drop n' bs = drop n (bs' @ take m bs) @ drop m bs"
        proof -
          have "n' \<le> m"
            using n'_def True m_leq_bs lassms(1)
            by auto
          then have "drop n' bs = drop n' (take m bs) @ drop m bs"
            using m_leq_bs
            by (rule drop_take_drop)
          moreover have "\<dots> = drop n (bs' @ take m bs) @ drop m bs"
            using m_leq_bs True
            by (auto simp add: n'_def)
          finally show ?thesis .
        qed
        then show ?thesis
          using lassms(3)
          by auto
      qed
      ultimately have "n' \<ge> m"
        using qs_intro[OF q_Q n'_le_bs] assms(3) Min_le[OF snd_qs(1)] by fastforce
      then show ?thesis
        using n'_def True lassms(1) by auto
    next
      case False
      then show ?thesis
        using lassms(2,3) m_leq_bs min nat_le_linear by auto
    qed
  qed
  moreover have "(case b of Blank \<Rightarrow> True | Symb b' \<Rightarrow>
    (\<forall>q b'' bs''. \<not>(init \<leadsto>(as', (bs' @ take m bs) @ drop m bs @ b'' # bs'') q \<and> active q [])))"
    using assms(1) m_leq_bs
    apply (auto simp add: tdfa_inv_def split: Al.splits)
    by (metis append_assoc append_take_drop_id)
  ultimately have "tdfa_inv as' (bs' @ take m bs) (drop m bs) b qs'"
    using assms(1) m_leq_bs
    apply (auto simp add: tdfa_inv_def qs'_def drop_qs_def)
     apply (metis add.commute take_add)
    by (metis add.commute take_add)
  then show "m \<le> length bs \<and> tdfa_inv_aligned as' (bs' @ take m bs) (drop m bs) b (drop_qs m qs)"
    unfolding qs'_def[symmetric] tdfa_inv_aligned_def
    using m_leq_bs qm_zero by auto
qed

lemma tdfa_inv_ext_qs: "tdfa_inv as' bs' bs (Symb b) qs \<Longrightarrow>
  tdfa_inv as' bs' (bs @ [b]) x (ext_qs b bs qs)"
proof -
  assume assms: "tdfa_inv as' bs' bs (Symb b) qs"
  have assms': "(\<forall>q b'' bs''. \<not>(init \<leadsto>(as', bs' @ bs @ b'' # bs'') q \<and> active q []))"
    using assms(1) by (auto simp add: tdfa_inv_def)
  define qs' where "qs' = ext_qs b bs qs"
  have qs'_sub_qs: "qs' \<subseteq> qs"
    by (auto simp add: qs'_def ext_qs_def)
  have qs_sub: "qs \<subseteq> Q \<times> {0..length bs}"
    using assms(1) by (auto simp add: tdfa_inv_def)
  then have snd_qs': "finite (snd ` qs')"
    using finite_Q qs'_sub_qs by (auto simp add: qs'_def finite_subset)
  have qs_dest: "\<And>q n. (q, n) \<in> qs \<Longrightarrow>
    q \<in> Q \<and> n \<le> length bs \<and> init \<leadsto>(as', bs' @ take n bs) q \<and> active q (drop n bs)"
    using assms(1) by (auto simp add: tdfa_inv_def ext_qs_def)
  then have qs'_dest: "\<And>q n. (q, n) \<in> qs' \<Longrightarrow>
    q \<in> Q \<and> n \<le> length (bs @ [b]) \<and> init \<leadsto>(as', bs' @ take n (bs @ [b])) q \<and>
    active q (drop n (bs @ [b]))"
    by (fastforce simp add: qs'_def ext_qs_def)
  have qs_intro: "\<And>q n. q \<in> Q \<Longrightarrow> n \<le> length bs \<Longrightarrow> init \<leadsto>(as', bs' @ take n bs) q \<Longrightarrow>
    active q (drop n bs) \<Longrightarrow> (q, n) \<in> qs"
    using assms(1) by (auto simp add: tdfa_inv_def)
  have qs'_intro: "\<And>q n. q \<in> Q \<Longrightarrow> n \<le> length (bs @ [b]) \<Longrightarrow>
    init \<leadsto>(as', bs' @ take n (bs @ [b])) q \<Longrightarrow> active q (drop n (bs @ [b])) \<Longrightarrow> (q, n) \<in> qs'"
  proof -
    fix q n
    assume lassms: "q \<in> Q" "n \<le> length (bs @ [b])" "init \<leadsto>(as', bs' @ take n (bs @ [b])) q"
      "active q (drop n (bs @ [b]))"
    have n_le: "n \<le> length bs"
      using assms' lassms(3) active_mono lassms(2,4)
      by fastforce
    then show "(q, n) \<in> qs'"
      using lassms(3,4) qs_intro[OF lassms(1) n_le] active_mono
      by (auto simp add: qs'_def ext_qs_def)
  qed
  have "\<And>q n. n \<le> length bs' \<Longrightarrow> init \<leadsto>(as', take n bs') q \<Longrightarrow> active q (drop n bs' @ bs) \<Longrightarrow>
    n = length bs'"
    using assms(1) by (auto simp add: tdfa_inv_def)
  then have "\<And>q n. n \<le> length bs' \<Longrightarrow> init \<leadsto>(as', take n bs') q \<Longrightarrow>
    active q (drop n bs' @ (bs @ [b])) \<Longrightarrow> n = length bs'"
    using active_mono by auto
  moreover have "(case x of Blank \<Rightarrow> True | Symb b' \<Rightarrow>
    (\<forall>q b'' bs''. \<not>(init \<leadsto>(as', bs' @ (bs @ [b]) @ b'' # bs'') q \<and> active q [])))"
    using assms' by (auto split: Al.splits)
  ultimately show "tdfa_inv as' bs' (bs @ [b]) x (ext_qs b bs qs)"
    unfolding tdfa_inv_def qs'_def[symmetric]
    using qs'_dest qs'_intro by fast
qed

lemma tdfa_inv_drop_upd_qs: "tdfa_inv_aligned as' bs' bs
  (if length bs \<ge> K' then ext_b else Blank) qs \<Longrightarrow>
  qs' = upd_qs a bs qs \<Longrightarrow> qs' \<noteq> {} \<Longrightarrow> m = Min (snd ` qs') \<Longrightarrow> m \<le> length bs \<and>
  tdfa_inv_aligned (as' @ [a]) (bs' @ take m bs) (drop m bs)
  (if length bs \<ge> K' then ext_b else Blank) (drop_qs m qs')"
  apply (rule tdfa_inv_drop_qs)
  using tdfa_inv_upd_qs by (auto split: if_splits Al.splits)

lemma tdfa_inv_drop_ext_qs: "tdfa_inv_aligned as' bs' bs (Symb b) qs \<Longrightarrow>
  qs' = ext_qs b bs qs \<Longrightarrow> qs' \<noteq> {} \<Longrightarrow> m = Min (snd ` qs') \<Longrightarrow> m \<le> length (bs @ [b]) \<and>
  tdfa_inv_aligned as' (bs' @ take m (bs @ [b])) (drop m (bs @ [b])) x (drop_qs m qs')"
  apply (rule tdfa_inv_drop_qs)
  using tdfa_inv_ext_qs by (auto simp add: tdfa_inv_aligned_def)

lemma \<tau>_tdfa_\<tau>: "q \<leadsto>(as, drop n bs @ bs'') q' \<Longrightarrow> accept q' \<Longrightarrow>
  init \<leadsto>(as', bs' @ take n bs) q \<Longrightarrow> q \<in> Q \<Longrightarrow> n \<le> length bs \<Longrightarrow>
  STATE (bs, qs) \<in> tdfa_Q \<Longrightarrow> tdfa_inv_aligned as' bs' bs (safe_hd bs'') qs \<Longrightarrow>
  \<exists>r. tdfa.computation (STATE (bs, qs)) ((as, []), (bs'', [])) r \<and> tdfa_accept r"
proof (induction q "(as, drop n bs @ bs'')" q' arbitrary: n as bs bs'' as' bs' qs
  rule: computation.induct)
  case (base q)
  then have "(q, n) \<in> qs"
    by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def active_def)
  then show ?case
    using base(1,2,5,6,7)
    by (auto simp: tdfa_inv_aligned_def tdfa_inv_def active_def
        intro!: exI[of _ "STATE (bs, qs)"]) (auto simp: tdfa_accept_def)
next
  case (step q a q' cs as cs' q'')
  then show ?case
  proof (induction bs'' arbitrary: n as bs as' bs' qs)
    case Nil
    define qs' where "qs' = upd_qs a bs qs"
    define m where "m = Min (snd ` qs')"
    have n_cs_le_bs: "n + length cs \<le> length bs"
      using Nil(4,8)
      by (metis Nat.le_diff_conv2 add.commute le_add1 length_append length_drop self_append_conv)
    have cs'_def: "cs' = drop (n + length cs) bs"
      using Nil(4)
      by (metis add.commute append_Nil2 append_eq_conv_conj drop_drop)
    have act_q: "active q (drop n bs)"
      using Nil(1,2,4,5)
      apply (auto simp add: active_def)
      by (metis Nil.prems(4) computation.step)
    have act_q': "active q' (drop (n + length cs) bs)"
      using Nil(2,5)
      apply (auto simp add: active_def cs'_def)
      by (metis append.right_neutral)
    define x where "x = (q, n)"
    have q_n_qs: "(q, n) \<in> qs"
      using act_q Nil(6,7,8,9,10)
      by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
    have fin_qs: "finite qs"
      using finite_tdfa_Q_qs Nil(9) by auto
    have cs_take: "cs = take (length cs) (drop n bs)"
      using Nil(1,4)
      by (metis append_Nil2 append_eq_conv_conj)
    have q'_qs': "(q', n + length cs) \<in> qs'"
      using Nil(1) cs_take Nil(4) act_q' n_cs_le_bs q_n_qs
      by (auto simp add: x_def qs'_def upd_qs_def intro: bexI[of _ "x"])
    then have qs'_nonempty: "qs' \<noteq> {}"
      by auto
    have qs_sub: "qs \<subseteq> Q \<times> {0..length bs}"
      using Nil(9) by (auto simp add: tdfa_Q_def)
    then have qs'_sub: "qs' \<subseteq> Q \<times> {0..length bs}"
      using \<delta>_closed by (auto simp add: qs'_def upd_qs_def)
    then have snd_qs': "finite (snd ` qs')" "snd ` qs' \<noteq> {}"
      using finite_Q finite_subset qs'_nonempty by fastforce+
    have m_n_cs: "m \<le> n + length cs"
      using m_def Min_le[OF snd_qs'(1)] q'_qs' by fastforce
    have inv': "m \<le> length bs \<and> tdfa_inv_aligned (as' @ [a]) (bs' @ take m bs) (drop m bs) Blank
      (drop_qs m qs')"
      using tdfa_inv_drop_upd_qs[OF _ qs'_def qs'_nonempty m_def, of as' bs'] Nil(10)
      by (cases "K' \<le> length bs") (auto simp: safe_hd_def)
    have q'_Q: "q' \<in> Q"
      using Nil(1,7) \<delta>_closed by auto
    have drop_tdfa_Q: "STATE (drop m bs, drop_qs m qs') \<in> tdfa_Q"
      using qs'_def m_def drop_qs_tdfa_Q[OF upd_qs_tdfa_Q, OF Nil(9)] qs'_nonempty
      by (auto simp add: qs'_def m_def)
    have init': "init \<leadsto>(as' @ [a], (bs' @ take m bs) @ take (n + length cs - m) (drop m bs)) q'"
      using Nil(1,6) cs_take
      by (metis append.assoc computation_snoc le_add_diff_inverse m_n_cs take_add)
    have cs'_def': "cs' = drop (n + length cs - m) (drop m bs)"
      using cs'_def m_n_cs by auto
    obtain r where r_def:
      "tdfa.computation (STATE (drop m bs, drop_qs m qs')) ((as, []), ([], [])) r" "tdfa_accept r"
      using Nil(3)[OF _ Nil(5) init' q'_Q _ drop_tdfa_Q, of "[]"] n_cs_le_bs m_n_cs
        cs'_def conjunct2[OF inv'] cs'_def'
      by (fastforce simp: safe_hd_def)
    have step: "tdfa_step (STATE (bs, qs)) (Symb a, Blank) =
      Some (STATE (drop m bs, drop_qs m qs'), True, False)"
      using qs'_def m_def qs'_nonempty Nil(9)
      by (cases "length bs \<ge> K'") (auto simp: Let_def)
    show ?case
      using r_def(1,2) step
      by (auto simp: safe_hd_def intro!: exI[of _ r])
  next
    case (Cons b bs'')
    have q_q'': "q \<leadsto>(a # as, drop n bs @ b # bs'') q''"
      using Cons(2,3,5)
      using computation.step by fastforce
    have act_q_cs: "active q cs"
      using q_q'' Cons(5,6) active_mono
      by (metis active_def)
    have act_q: "active q (drop n bs @ b # bs'')"
      using q_q'' Cons(6)
      apply (auto simp add: active_def)
      by (metis (full_types) append_Nil2)
    then have act_q_b: "active q (drop n bs @ [b])"
      using active_mono by auto
    have q_n_qs: "(q, n) \<in> qs"
      using Cons(7,8,9,11) act_q
      by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def active_def)
    have q'_Q: "q' \<in> Q"
      using Cons(2,8) \<delta>_closed by auto
    show ?case
    proof (cases "length bs \<ge> K'")
      case True
      define qs' where "qs' = upd_qs a bs qs"
      define m where "m = Min (snd ` qs')"
      have qs_sub: "qs \<subseteq> Q \<times> {0..length bs}"
        using Cons(10) by (auto simp add: tdfa_Q_def)
      have n_cs_le_bs: "n + length cs \<le> length bs"
      proof -
        have "finite qs"
          using finite_Q finite_subset qs_sub by auto
        obtain qm where "(qm, 0) \<in> qs"
          using Cons(11) by (auto simp add: tdfa_inv_aligned_def)
        then have init_qm: "init \<leadsto>(as', bs') qm" "active qm bs"
          using Cons(11) by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
        have init_q: "init \<leadsto>(as', bs' @ take n bs) q" "active q (drop n bs)"
          using q_n_qs Cons(11) by (auto simp add: tdfa_inv_aligned_def tdfa_inv_def)
        have act_q_empty: "active q []"
          using init_q(2) active_mono by auto
        have act_qm: "active qm (take n bs)"
          using init_qm(2) Cons(9) active_mono
          by (metis append_take_drop_id)
        have "n \<le> K"
          using bounded'[OF init_q(1) act_q_empty init_qm(1) act_qm] Cons(9) by auto
        moreover have "length cs \<le> output_speed"
          using output_speed_step Cons(2,8) by auto
        ultimately show ?thesis
          using True unfolding K'_def by auto
      qed
      have cs'_def: "cs' = drop (n + length cs) bs @ b # bs''"
        using Cons(5) n_cs_le_bs
        by (metis Cons.prems(8) add.commute add_le_imp_le_left append_eq_append_conv_if drop_drop
            le_add_diff_inverse length_drop)
      have act_q': "active q' (drop (n + length cs) bs)"
        using act_q Cons(2) n_cs_le_bs
        apply (auto simp add: active_def)
        by (metis cs'_def step.hyps(2) step.prems(1))
      define x where "x = (q, n)"
      have cs_take: "cs = take (length cs) (drop n bs)"
        using n_cs_le_bs Cons(5) append_eq_conv_conj cs'_def
        by auto
      have q'_qs': "(q', n + length cs) \<in> qs'"
        using cs_take act_q' n_cs_le_bs q_n_qs upd_qs_def Cons(2)
        by (auto simp add: x_def qs'_def upd_qs_def intro!: bexI[of _ "x"])
      then have qs'_nonempty: "qs' \<noteq> {}"
        by auto
      have qs'_sub: "qs' \<subseteq> Q \<times> {0..length bs}"
        using qs_sub \<delta>_closed by (auto simp add: qs'_def upd_qs_def)
      then have snd_qs': "finite (snd ` qs')" "snd ` qs' \<noteq> {}"
        using finite_Q finite_subset qs'_nonempty by fastforce+
      have m_n_cs: "m \<le> n + length cs"
        using m_def Min_le[OF snd_qs'(1)] q'_qs' by fastforce
      have inv': "m \<le> length bs \<and> tdfa_inv_aligned (as' @ [a]) (bs' @ take m bs) (drop m bs)
        (Symb b) (drop_qs m qs')"
        using tdfa_inv_drop_upd_qs[OF _ qs'_def qs'_nonempty m_def, of as' bs'] Cons(11) True
        by (auto simp: safe_hd_def)
      have q'_Q: "q' \<in> Q"
        using Cons(2,8) \<delta>_closed by auto
      have drop_tdfa_Q: "STATE (drop m bs, drop_qs m qs') \<in> tdfa_Q"
        using qs'_def m_def drop_qs_tdfa_Q[OF upd_qs_tdfa_Q] Cons(10) qs'_nonempty
        by (auto simp add: qs'_def m_def)
      have init': "init \<leadsto>(as' @ [a], (bs' @ take m bs) @ take (n + length cs - m) (drop m bs)) q'"
        using Cons(2,7) cs_take m_n_cs computation_snoc
        by (metis append.assoc le_add_diff_inverse take_add)
      have cs'_def': "cs' = drop (n + length cs - m) (drop m bs) @ b # bs''"
        using cs'_def m_n_cs by auto
      obtain r where r_def:
        "tdfa.computation (STATE (drop m bs, drop_qs m qs')) ((as, []), (b # bs'', [])) r"
        "tdfa_accept r"
        using Cons(4)[OF _ _ init' q'_Q _ drop_tdfa_Q, of "b # bs''"] Cons(6) n_cs_le_bs m_n_cs
          cs'_def conjunct2[OF inv'] cs'_def'
        by (auto simp: safe_hd_def) fastforce
      have step: "tdfa_step (STATE (bs, qs)) (Symb a, Symb b) =
        Some (STATE (drop m bs, drop_qs m qs'), True, False)"
        using Cons(10) qs'_def m_def qs'_nonempty True
        by (auto simp: Let_def)
      show ?thesis
        using r_def(1,2) step
        by (auto simp: safe_hd_def intro!: exI[of _ r])
    next
      case False
      define qs' where "qs' = ext_qs b bs qs"
      define m where "m = Min (snd ` qs')"
      have qs'_nonempty: "qs' \<noteq> {}"
        using q_n_qs Cons(9) act_q_b
        by (fastforce simp add: qs'_def ext_qs_def)
      have step: "tdfa_step (STATE (bs, qs)) (Symb a, Symb b) =
        Some (STATE (drop m (bs @ [b]), drop_qs m qs'), False, True)"
        using Cons(10) qs'_def m_def qs'_nonempty False
        by (auto simp: Let_def)
      have inv': "m \<le> length (bs @ [b]) \<and> tdfa_inv_aligned as' (bs' @ take m (bs @ [b]))
        (drop m (bs @ [b])) (safe_hd bs'') (drop_qs m qs')"
        using Cons(11) tdfa_inv_drop_ext_qs[OF _ qs'_def qs'_nonempty m_def]
        by (auto simp: safe_hd_def)
      have drop_tdfa_Q: "STATE (drop m (bs @ [b]), drop_qs m (ext_qs b bs qs)) \<in> tdfa_Q"
        using qs'_def m_def drop_qs_tdfa_Q[OF ext_qs_tdfa_Q, OF Cons(10)] False qs'_nonempty
        by (auto simp add: qs'_def m_def)
      have q_n_qs': "(q, n) \<in> qs'"
        using q_n_qs Cons(9) act_q_b
        by (auto simp add: qs'_def ext_qs_def)
      have qs_sub: "qs \<subseteq> Q \<times> {0..length bs}"
        using Cons by (auto simp add: tdfa_Q_def)
      then have qs'_sub: "qs' \<subseteq> Q \<times> {0..length bs}"
        by (auto simp add: qs'_def ext_qs_def)
      then have snd_qs': "finite (snd ` qs')" "snd ` qs' \<noteq> {}"
        using finite_Q finite_subset qs'_nonempty by fastforce+
      have m_n: "m \<le> n"
        using q_n_qs' m_def Min_le[OF snd_qs'(1)] by fastforce
      have cs_app_cs': "cs @ cs' = drop (n - m) (drop m (bs @ [b])) @ bs''"
        using m_n conjunct1[OF inv'] Cons by auto
      have "n - m \<le> length (drop m (bs @ [b]))"
        using conjunct1[OF inv'] Cons by auto
      moreover have "init \<leadsto>(as', (bs' @ take m (bs @ [b])) @ take (n - m) (drop m (bs @ [b]))) q"
        using Cons(7) m_n conjunct1[OF inv']
        by (metis Cons.prems(8) append_Nil2 append_eq_append_conv2 append_eq_conv_conj
            diff_is_0_eq' le_add_diff_inverse list.size(3) take_add take_append)
      ultimately obtain r where r_def: "tdfa.computation (STATE (drop m (bs @ [b]), drop_qs m qs'))
        ((a # as, []), (bs'', [])) r" "tdfa_accept r"
        using Cons(1)[OF Cons(2) Cons(3) _ cs_app_cs' Cons(6) _ Cons(8) _
          drop_tdfa_Q[folded qs'_def] conjunct2[OF inv']] Cons(4) m_n conjunct1[OF inv']
        by fast
      show ?thesis
        using r_def(1,2) step
        by (auto simp: safe_hd_def intro!: exI[of _ r])
    qed
  qed
qed

lemma tdfa_\<tau>_\<tau>: "tdfa.computation (STATE (bs, qs)) ((as, []), (bs'', [])) r \<Longrightarrow>
  tdfa_accept r \<Longrightarrow> tdfa_inv_aligned as' bs' bs (safe_hd bs'') qs \<Longrightarrow>
  (as' @ as, bs' @ bs @ bs'') \<in> \<tau>"
proof (induction "STATE (bs, qs)" "((as, [] :: 'a list), (bs'', [] :: 'b list))" r
    arbitrary: bs qs as bs'' as' bs' rule: tdfa.computation.induct)
  case base
  obtain q n where qn_def: "(q, n) \<in> qs" "accept q" "n = length bs"
    using base(1)
    by (auto simp: tdfa_accept_def)
  then show ?case
    using base(2)
    by (fastforce simp add: tdfa_inv_aligned_def tdfa_inv_def \<tau>_def)
next
  case (step_TF a bs'' q' as q'')
  define qs' where "qs' = upd_qs a bs qs"
  define m where "m = Min (snd ` qs')"
  have props: "qs' \<noteq> {}" "q' = STATE (drop m bs, drop_qs m qs')"
    using qs'_def m_def step_TF(1)
    by (auto simp: safe_hd_def Let_def split: list.splits if_splits)
  have "\<not>K' \<le> length bs \<Longrightarrow> bs'' = []"
    using step_TF(1)
    by (cases bs'') (auto simp: safe_hd_def Let_def split: if_splits)
  then have "m \<le> length bs \<and>
    tdfa_inv_aligned (as' @ [a]) (bs' @ take m bs) (drop m bs) (safe_hd bs'') (drop_qs m qs')"
    using tdfa_inv_drop_upd_qs[OF _ qs'_def props(1) m_def, of as' bs'] step_TF(5)
    by (cases "K' \<le> length bs") (auto simp: safe_hd_Nil split: list.splits)
  then show ?case
    using step_TF(3)[OF props(2) step_TF(4), of "as' @ [a]" "bs' @ take m bs"]
    by auto (metis append.assoc append_take_drop_id)
next
  case (step_FT as b q' bs'' q'' bs)
  define qs' where "qs' = ext_qs b bs qs"
  define m where "m = Min (snd ` qs')"
  have props: "length bs < K'" "qs' \<noteq> {}" "q' = STATE (drop m (bs @ [b]), drop_qs m qs')"
    using qs'_def m_def step_FT(1)
    by (auto simp: safe_hd_def Let_def split: list.splits if_splits)
  have inv: "m \<le> length (bs @ [b])" "tdfa_inv_aligned as' (bs' @ take m (bs @ [b]))
    (drop m (bs @ [b])) (safe_hd bs'') (drop_qs m qs')"
    using tdfa_inv_drop_ext_qs[OF _ qs'_def props(2) m_def] step_FT(5)
    by (auto simp: safe_hd_def)
  show ?case
    using step_FT(3)[OF props(3) step_FT(4) inv(2)] inv(1)
    by (metis append.assoc append_Cons append_Nil append_take_drop_id)
qed (auto simp: Let_def split: if_splits)

lemma comp_REJECT_ACCEPT:
  "tdfa.computation q ((as, as'), bs, bs') q' \<Longrightarrow> q = REJECT \<Longrightarrow> tdfa_accept q' \<Longrightarrow> False"
  by (drule tdfa.comp_unreachable) (auto simp: tdfa_accept_def)

lemma not_active_init: "\<not>active init [] \<Longrightarrow> tdfa.\<tau> = \<tau>"
  using comp_REJECT_ACCEPT
  unfolding tdfa.\<tau>_def
  by (force simp add: active_def tdfa_init_def \<tau>_def)

lemma tdfa_\<tau>_sub_\<tau>: "tdfa.\<tau> \<subseteq> \<tau>"
  using tdfa_\<tau>_\<tau>[OF _ _ tdfa_inv_init] not_active_init
  unfolding tdfa.\<tau>_def
  unfolding tdfa_init_def tdfa_accept_def
  by auto

lemma \<tau>_sub_tdfa_\<tau>: "\<tau> \<subseteq> tdfa.\<tau>"
  using init_in_tdfa_Q
  unfolding \<tau>_def tdfa.\<tau>_def
  unfolding tdfa_init_def
  using \<tau>_tdfa_\<tau>[of init _ 0 "[]" _ _ "[]" "[]"] init_in_Q tdfa_inv_init
  by (fastforce simp: active_def split: if_splits)

(* Theorem 9 *)
lemma tdfa_correct: "\<tau> = tdfa.\<tau>"
  using tdfa_\<tau>_sub_\<tau> \<tau>_sub_tdfa_\<tau> by auto

end

end

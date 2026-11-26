module

public import Meyniel

@[expose] public section

-- The posted proof and its game-theoretic consequences.
#check Meyniel.oneCop_lemma
#check Meyniel.copNumber_three_quarters
#check Meyniel.weak_meyniel_for_epsilon
#check Meyniel.weak_meyniel_conjecture
#check MeynielConjecture.meyniel_conjecture.variants.soft

-- Two formulations of the multiscale bound.
#check Meyniel.copNumber_two_thirds_epsilon
#check Meyniel.copNumber_two_thirds_little_o
#check MeynielConjecture.copNumber_two_thirds_little_o

#print axioms Meyniel.RandomConclusion.exists_covering_tape
#print axioms Meyniel.oneCop_lemma
#print axioms Meyniel.copNumber_three_quarters
#print axioms Meyniel.weak_meyniel_for_epsilon
#print axioms Meyniel.weak_meyniel_conjecture
#print axioms MeynielConjecture.copNumber_eq
#print axioms MeynielConjecture.meyniel_conjecture.variants.soft
#print axioms Meyniel.Multiscale.ball_clock_mixture
#print axioms Meyniel.Multiscale.terminal_trials
#print axioms Meyniel.copNumber_two_thirds_epsilon
#print axioms Meyniel.copNumber_two_thirds_little_o
#print axioms MeynielConjecture.copNumber_two_thirds_little_o

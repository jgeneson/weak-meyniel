# The weak Meyniel conjecture in Lean 4

This repository contains two proofs about the cop number `c(G)` of a finite connected undirected graph with `n` vertices.

| Result | Lean theorem |
| --- | --- |
| **Three-page proof.** Every such graph satisfies `c(G) ≤ 31 n^(3/4) log(2n)`, with the natural logarithm. | [Meyniel.copNumber_three_quarters](Meyniel/Theorem.lean) |
| **Multiscale proof.** For every real `ε > 0` there is a constant `C(ε) > 0` such that every such graph satisfies `c(G) ≤ C(ε) n^(2/3 + ε)`. | [Meyniel.copNumber_two_thirds_epsilon](Meyniel/TwoThirds.lean) |
| **Vanishing exponent.** There is a single function `e(n) > 0` tending to zero such that every such graph satisfies `c(G) ≤ n^(2/3 + e(n))`. This gives the bound `n^(2/3 + o(1))`. | [Meyniel.copNumber_two_thirds_little_o](Meyniel/TwoThirds.lean) |

The first proof follows Jesse Geneson's posted paper. The constant 31 makes the paper's big-O estimate explicit. The multiscale argument is a separate proof of the stronger bound. [Three-page manuscript](https://www.researchgate.net/publication/418284188_The_weak_Meyniel_conjecture_is_true)

Lu and Peng proved the upper bound $n\,2^{-(1-o(1))\sqrt{\log_2 n}}$. Scott and Sudakov obtained it independently. Frieze, Krivelevich and Loh recovered it as the speed-one case of their theorem allowing a faster robber. Written as a power of $n$, the exponent in this earlier bound tends to $1$. The multiscale bound here gives a fixed saving in the exponent. [Lu and Peng](https://doi.org/10.1002/jgt.20642) · [Scott and Sudakov](https://doi.org/10.1137/100812963) · [Frieze, Krivelevich and Loh](https://doi.org/10.1002/jgt.20591)

## The Palomar statements

The Challenge gives the complete rules of the game and two theorem statements. `PalomarMeyniel.twoThirds` says that the **same** error function tending to zero bounds every finite connected graph of each order. `PalomarMeyniel.soft` gives the weak conjecture with one positive exponent saving and one positive constant for all graphs. In the Solution, the first theorem invokes the multiscale proof, and the second follows from it by taking an exponent saving of `1/4`. The conjectured square-root upper bound remains open. [Auditable game and statements](Challenge.lean) · [Solution](Solution.lean)

For Palomar, the two `sorry` lines in the Challenge mark exactly the statements to compare. Each has a corresponding proof in the separately built Solution. The Comparator configuration identifies those two names. The project metadata gives the sources, the role of Codex with GPT-6.2 Astra Ultra, and the verification history. [Comparator configuration](comparator.json) · [Metadata](formalization.yaml)

## Verify on macOS or Linux

Install Git and the Lean toolchain manager, elan. Open a terminal in the folder containing `lean-toolchain` and run the command below. The port targets Lean 4.35.0, with the matching Mathlib revision pinned in `lake-manifest.json`. The first run needs internet access and several GiB of disk space for Lean, Mathlib and its compiled cache. [Install Lean and elan](https://lean-lang.org/install/)

```sh
sh verify.sh
```

The script checks for the two intended Challenge placeholders, scans every other project Lean file for placeholders, and builds the library, Challenge and Solution. It then imports the **Solution** into a fresh Lean process, checks both advertised theorem names and the 12 original proof declarations, and rejects any axiom outside `propext`, `Classical.choice` and `Quot.sound`. A proof that depended on a placeholder would report `sorryAx`. A successful run ends with `PASS`. On failure the script exits with a nonzero status and prints the diagnostic. [Verification script](verify.sh) · [Original checks](Checks.lean)

To repeat those checks and replay the compiled proof library and the two Solution declarations through Lean's kernel, run the following command. Replay can take several minutes per module.

```sh
sh verify.sh --replay
```

## Compare the Challenge with the Solution

On Linux with Git and a working `bubblewrap` (`bwrap`) installation, run this in the same folder after building. This command uses Lean 4.35's Comparator to compare both formal statements and their dependency definitions across the two modules. The checked-in configuration also requests the bundled NanoDa checker.

```sh
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --config comparator.json
```

On macOS the two `verify.sh` commands above run natively. For the sandboxed Comparator step use Linux, such as a Linux VM with `bwrap`. Palomar performs its own mechanical verification against the submitted public commit. The matching root license is Apache-2.0. [Palomar submission guide](https://palomar-registry.org/how-to-submit) · [Repository license](LICENSE)

## The game

The cops place themselves before the robber chooses a starting vertex. Each player may stay put or move along an edge. All positions are visible. In each round the cops move first. Capture occurs as soon as a cop and the robber occupy the same vertex. The winning condition allows the robber to choose each move after seeing the cops' moves. The cop number is the least size of a winning team. [Game.lean](Meyniel/Game.lean)

The project also proves that this cop number equals the one defined in Google DeepMind's Formal Conjectures project. It proves the upstream soft conjecture statement with its original quantifiers and also gives the vanishing-exponent bound using that project's cop number. [Comparison proof](Meyniel/CompareGame.lean) · [Upstream statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MeynielConjecture.lean) · [Upstream license](LICENSES/Apache-2.0.txt)

## The three-page proof

| Step | Source |
| --- | --- |
| Extend the test walks to a common vertex. Compare the guess weights along each diagonal and multiply the bounds down the columns. | [Extension](Meyniel/Extension.lean) · [Weights](Meyniel/Weights.lean) · [Diagonals](Meyniel/Interception.lean) |
| Implement the cop's resampling rule by a tape of random choices. Prove that a surviving terminal guess catches the robber and fix one tape for the prescribed family. | [Policy](Meyniel/RandomPolicy.lean) · [Distribution](Meyniel/RandomLaw.lean) · [Capture](Meyniel/RandomCapture.lean) · [Fixing the tape](Meyniel/RandomConclusion.lean) |
| Obtain a deterministic cop catching at least a `1 / sqrt(2n)` fraction of **any nonempty family** of walks at the paper's deadline. Repeat on the walks still uncovered. | [One-cop lemma](Meyniel/Theorem.lean) · [Cover and adaptive game](Meyniel/Cover.lean) · [Bounded diameter](Meyniel/Bounds.lean) |
| Guard shortest paths, deploy the other cops in the remaining component, and balance the two team sizes. | [Path guards](Meyniel/Guard.lean) · [Optimization](Meyniel/Optimize.lean) · [Theorem](Meyniel/Theorem.lean) |

The uniform distribution in the one-cop calculation counts walks in the prescribed family. The team obtained from the cover wins against every legal sequence of robber responses.

## The multiscale proof

| Step | Source |
| --- | --- |
| For every law on a finite family of walks, bound the best expected weighted capture using conditional entropy. Finite minimax gives a single mixture with a capture bound for each walk. | [Entropy](Meyniel/MultiscaleEntropy.lean) · [Finite minimax](Meyniel/MultiscaleMinimax.lean) · [Window minimax](Meyniel/MultiscaleWindowMinimax.lean) |
| Guess a vertex in a ball around a future position. Bound legal travel between guesses, conditional on the visible prefix, and iterate on a clock with nonunit steps. | [Smoothed guesses](Meyniel/MultiscaleSmoothing.lean) · [Travel between targets](Meyniel/MultiscaleTargets.lean) · [Graph clock](Meyniel/MultiscaleGraphClock.lean) · [Capture estimate](Meyniel/MultiscaleBallClock.lean) |
| When a trial reaches a correct prediction, run a shorter trial inside it. Average the resulting capture estimates across radii and time offsets to cover the global and local windows. | [Recursive trials](Meyniel/MultiscaleTerminalTrials.lean) · [Offset averaging](Meyniel/MultiscaleOffset.lean) · [Root prices](Meyniel/MultiscaleRootPrice.lean) · [Global and local cases](Meyniel/MultiscaleRootCases.lean) |
| Select deterministic covers and deploy guards from the robber's trail. Count the cops needed for overlapping assignments and apply the diameter reduction. | [Walk covers](Meyniel/MultiscaleCover.lean) · [Guard deployment](Meyniel/MultiscaleDeployment.lean) · [Team budget](Meyniel/MultiscaleBudget.lean) · [Diameter step](Meyniel/MultiscaleAssembly.lean) |
| Sum the cost over successive halvings of the diameter and absorb the order thresholds into a constant for each fixed `ε`. Diagonalize over positive slacks to obtain a single vanishing exponent. | [Diameter bounds](Meyniel/MultiscaleBounds.lean) · [Vanishing exponent](Meyniel/MultiscaleLimit.lean) · [Theorems](Meyniel/TwoThirds.lean) |

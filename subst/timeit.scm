(optimize-level 2)
(include "mkstats.scm")
(include "settings.scm")
(include "skew-bral-def.scm")
(include "skew-bral.scm")
(include "bst.scm")
(include "trie.scm")
(include "mk.scm")
(include "mktests.scm")
(include "permo.scm")
(include "zebra.scm")
(include "alphatap.scm")
(include "walktests.scm")
(module
  ()
  (import scheme mkstats settings mk mktests permo walktests)
  (run-all-walktests))

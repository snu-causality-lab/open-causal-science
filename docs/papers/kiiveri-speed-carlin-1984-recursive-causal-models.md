# Kiiveri, Speed and Carlin (1984), recursive causal models

<!-- topic: Graphical Markov models -->

Example 3 contrasts a recursive factorization with the Markov
property of its undirected skeleton. In the directed model the
variables labelled 2 and 3 are independent given 1. The skeleton
would require independence given both 1 and 4.
[Paper, Example 3, p. 41](https://doi.org/10.1017/S1446788700027312)

[Example3.lean](../../OpenCausalScience/Papers/KiiveriSpeedCarlin1984/Example3.lean)
uses the printed covariance and concentration matrices in the order
`4,3,2,1`. It checks the covariance product of an explicit triangular
unit-noise coefficient matrix, verifies the matrix inverse, and finds
partial covariance zero given 1 and concentration entry one for the
pair 2,3. These are the exact matrix calculations supporting the
paper's Gaussian example. The general Gaussian equivalence between
zero partial covariance and conditional independence is a separate
probability theorem.

The companion on [directed Markov fields](lauritzen-et-al-1990-directed-markov-fields.md)
handles a finite rational law and its recursive factorization. The
1984 result additionally treats an undirected graph on the exogenous
variables.

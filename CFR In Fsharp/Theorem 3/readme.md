Date: 11/12/2019

Theorem 3 from the `Regret Minimization in Games with Incomplete Information` paper, approximately proven using FsCheck. Special thanks goes to Marc Lanctot for being patient in answering my questions and helping me when I got stuck.

This mini-project was remarkable for me in that for the first time it made me realize that theorem proving could be done without dependent type systems. Up to this point, I've thought of randomized testing as nothing other than a gimmick, but I see now that it is a fairly important thing as it opens the world of semi-formal mathematics to the low functional programming style as supported by languages like F#.

To me this is personally important, as it confirmed for me that with the right setup it is possible to substitute programming with mathematical talent, at least for something as simple as this particular theorem. More experimentation needs to be made to see how much of the domain of math randomized testing can cover. But finding the right math focus is something I've been looking for ages and I am very happy to finally have something.

The proof in this current form can serve as the basis for a full formalization in Agda or some other prover.

As the purpose of this experiment was to explain the theorem to myself rather than to the computer, I am going to skip that tedious work and instead see if I can approximately prove more difficult theorems. Based on how things have gone so far, I am optimistic about the prospects of this.
# Interaction Preserving Abstraction

We can consider any system as consisting of a set of state variables $V$ and a set of actions $A$. If we want to decompose the system, we can view it as a set of *modules*, where each module $M_i$ is simply a subset of actions $M_i \subseteq A$. Each action will be associated with some subset of state variables that it reads and/or writes. See [related paper](https://arxiv.org/abs/2202.11385) for similar formalization of these concepts, and also similar discussion in Section 4 of [this paper](https://cse.usf.edu/~haozheng/publications/tc10.pdf).

So, what it does mean for two modules to "interact"? If the two modules share no variables, then clearly there is no interaction between them. If they share variables, then they may interact in various ways. 

## Interaction with Unidirectional Data Flow

A basic case of interaction is when, for example, there is one shared variable $x_s$ between two modules, and one module $M_1$ writes to this variable  and the other module $M_2$ reads from it. In this case it is clear that whatever the behavior of $M_1$ is doesn't depend on any behavior of $M_2$ other than "how" $M_2$ writes to the shared variable $x_s$. This is, in a sense, a form of interaction with "unidirectional" data flow.

## Interaction with Bidirectional Data Flow

It may also be the case that interaction between two modules is not unidirectional in its data flow. For example, say there are 4 variables $x_1, x_{1 \rightarrow 2}, x_{2 \rightarrow 1}, x_2$ and two modules $M_1$ and $M_2$. Say that:

-  $M_1$ reads/writes $x_1$, writes $x_{1 \rightarrow 2}$, and reads from $x_{2 \rightarrow 1}$. 
-  $M_2$ reads/writes $x_2$, writes $x_{2 \rightarrow 1}$, and reads from $x_{1 \rightarrow 2}$. 
  
In this case, the behavior of $M_1$ depends on "how" $x_{1 \rightarrow 2}$ is updated, and on how it interacts with (internal) variable $x_1$. Similarly for $M_2$.

In this case, we can't only consider the behavior of either $M_1$ or $M_2$ in isolation, since their behavior is mutually dependent. So, in this case, if we wanted to verify the overall system composed of $M_1$ and $M_2$, we basically just have to verify the full (i.e. interleaving) composition $M_1 \mid\mid M_2$. 

If we know the interface that each module depends on for its behavior, though, we can come up with an abstraction of one submodule that preserves its behavior w.r.t this interface. In other words, it preserves the "interactions" between one component and another, and we can replace the original sub-component with a more abstract version, $\overset{\sim}{M_2}$. Then, we can verify $M_1 \mid\mid \overset{\sim}{M_2}$, as long as we are sure that $\overset{\sim}{M_2}$ is truly an "interaction preserving" abstraction" of $M_2$.

A question, then, is how to formally check that such an abstraction is actually interaction preserving? It seems we could verify this property by checking that, for every interaction variable $x_R$ that $M_2$ reads from, verify that $M_2 \Rightarrow \overset{\sim}{M_2}$ when letting the initial condition on these read input variables allow any possible (i.e. type-correct) value. 

Alternatively, I think it would be sufficient to simply check $(M_1 \mid\mid M_2) \Rightarrow \overset{\sim}{M_2}$ but this obviously has the drawback that you're required to verify the full, original composition $M_1 \mid\mid M_2$. I'm also not sure if this technically shows that $\overset{\sim}{M_2}$ is an interaction preserving abstraction of $M_2$. 
Rather, it seems to show that $\overset{\sim}{M_2}$ is an interaction preserving abstraction of $M_2$ *when operating in the context of* $M_1$. In practice, that seems to be all you really need to check, but might actually be a weaker property than showing interaction preservation in general.


# Finite-Automata-Toy
A small program for manipulating and visualising finite automata.

Contains functionality for running, manipulating, and viewing Finite Automata.
Available features include:
    * Reading in DFA, NFA from external files;
    * Checking whether a certain string is accepted by a given DFA, NFA;
    * Graceful handling of input symbols not in a machine's alphabet.
    * NFA <-> DFA conversion; in particular, NFA are run by deriving a DFA;
    * DFA minimisation;
    * Language operations include Union, Complement, Intersection,
      Star Closure, Concatenation, and Reversal;
    * Determination of equality between machines;
    * Identification of the empty and universally accepting machines;
    * Production of example strings accepted by a machine,
      and of the shortest string between two states;
    * Text description of DFA/NFA in the same format as in the external files
    * Interactive graph visualisation

Call demo() for a whirlwind tour of most of the major features.

Be aware that this was written first in Python 3.
There may be some unexpected breakage.


Invocation
==========

Program can be run with the following arguments:

--demo              | Calls demo()
--draw              | Launches the graph visualiser without loading a graph into it.
--draw filename     | Draws the DFA from an external file with a DFA or NFA in it

<string>            | checks <string> against a default DFA
<string> filename   | checks <string> against a DFA or NFA described in filename

--concat f1 f2      | Draws the graph of the concatenated machines described in f1 and f2
--union f1 f2       | Draws the graph of the union of the machines described in f1 and f2
--intersect f1 f2   | Draws the graph of the intersected machines described in f1 and f2

Graph Visualiser
================

Calling drawDFA on a machine will launch an interactive window containing a
graphical depiction of that machine. The window is resizeable, and pressing
Escape is a shortcut to exiting, along with the Quit button in the lower right.

States are grey circles. Those with thick outlines accept, those with thin
ones do not. The lighter state with a dashed outline is DFA's the start state.
Transitions are depicted by lines between circles, with the transition symbol
for that edge indicated nearer to the originating node, and an arrowhead at
the destination. Self loops are indicated by arcs on the top of nodes.
Their symbols hover above them.

Using your mouse, you may drag nodes of the graph around. If the simulation is
running, the rest of the graph will respond to your influence. However, if you
wish to arrange the graph without forces impeding you, the sim can be toggled
with the button in the top left corner. When the sim is not running, you may
also move the edge labels. You may wish to disable these, or enable State
labels: use the check boxes in the upper right for this purpose.
Dragging a node into the Delete Node box will remove it from the machine.
If you delete the start node of a machine, the result will be the empty machine
over the same alphabet.

The Minimise, Complement, Reverse and Star buttons will perform the language
operations they indicate. But there are some things to be mindful of.
First, they will tend to inflate the names of the machine's states. If you
have state labels enabled, this can become unsightly. To remedy this, use
the Redesignate button, which will rename the state alphabetically in BFS
order, starting from the start state.
Second, be wary of the Reverse and Star operations. They can easily generate
obscene bird's-nest graphs which will slow the program down even further than
its existing geriatric pace, or cause it to hang while it churns through
thousands of new states. Wherefore, exercise caution around large graphs.
The program already pre-minimises machines before performing the Star and
Reversal operations so as to forestall this. It leads to visually less
interesting results, but fewer interminable loops. But they still occur.
The Describe button will print a description of the current DFA to the terminal,
in case you want to save the machine you have arrived at.
If you check a string with the text field in the lower right, the trace of
checking the string against the current machine will be printed to the console.

Force coefficients may be adjusted with the sliders and text boxes in the
lower left. The radius sliders control the relaxation distance of a force:
there is repulsion inside this distance, attraction outside of it.
The text box constants are multipliers which determine a force's absolute
strength.

Finally, DFAs may be loaded from a file with the text box in the lower right.
If the file does not exist, or there was some error, the entry field will be
emptied and nothing will happen. Otherwise, the new machine will replace the
existing one.

Limitations: At present, there is no support for NFA. If you pass an one to
drawDFA, it will be first converted to a DFA before it is rendered.
Additionally, no more than one graph at a time can be displayed at the
moment, so there is no realistic way of presenting the binary language
operations such as union and concatenation.


Further Remarks
===============

Since this was built on the fly, and while learning tkinter, no rational design
was settled on from the start; it simply evolved from a DFA solver into
something larger. The internal distinction between NFA and DFA is unnecessary,
for example. The two could be unified, simplifying a number of operations.
Certainly the drawing loop could be made much more general and robust.

The visualisation, in particular, has obvious limitations. It would be an easy
extension to introduce rendering of NFA, but it leaves much to be desired
visually. The arrowheads are insubstantial, the self-loops are rigid, the
transition labels could be placed much more intelligently, the start state
could have an arrow pointing to it, accept states could be more clearly
delineated and so on. The most significant limitation, though, is that states
with mutual transitions display them on the same line, which makes it difficult
to discern at a glance whether two states both have transitions to one another
or not. Hypothetical future versions might consider using bezier curves instead
of lines for representing edges.

The sim, too, contains plenty of flaws. That everything, including gravity is
just a spring force diminishes the dynamism of the system, and introduces
bizarre aggregate behaviour, particularly for large graphs whose radius begins
to exceed the relaxation distance of gravity. There is possibly some scope
here for dynamically adjusting the coefficients of the simulation.
A physically-based, but more computationally expensive solution might be to
substitute an inverse-square attraction between nodes, and to add a repulsive
force which falls off as the inverse cube of the distance.
Still the question of scale is not solved, picking good coefficients may have
more art than science about it.
It might also be interesting to determine some means of discouraging edges
from crossing, but I don't know what form this would take, other than vague
notions of applying a torque. However, notions of mass, velocity, and
momentum would have to be introduced before such modifications could
realistically take place.
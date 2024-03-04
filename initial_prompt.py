from mistralai.client import MistralClient
from mistralai.models.chat_completion import ChatMessage
import os
import sys

sys.path.append(os.getcwd())
from utils.create import load_template

prompt = """Translate the informal solution into a sketch of the
formal Isabelle proof. Add `sledgehammer` in the sketch whenever
possible. `sledgehammer` will be used to call the automated Sledgehammer prover. 
Some conjectures will be specified in the prompt. Translate them into their formal Isabelle form
as lemmas, but do not prove them. When calling sledgehammer, use the lemmas as assumptions.
Here are some examples:

(* Problem\n\n
Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. 
Show that it is 12.

Solution\n\n
Let $y = x \\sin x$. It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}.\n
It is trivial to see that $y > 0$. \nThen one can multiply both sides by $y$ and 
it suffices to show $12y \\leq 9y^2 + 4$.\nThis can be done by the sum of squares method. 

Conjectures: {(9 * y^2 + 4) / y >= 12, y * sin y > 0}
*)

 
lemma y_positivity:
  fixes x::real
  assumes "0 < x" "x < pi"
  shows "x * sin x > 0"
proof -
  show ?thesis
  \<proof>
qed
lemma inequality_transformation:
  fixes y::real
  assumes "y > 0"
  shows "(9 * y^2 + 4) / y \<ge> 12"
proof -
  show ?thesis
  \<proof>
qed
theorem minimum_value_expression:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
proof -
  define y where "y=x * sin x"
  have c1 : "y > 0"
    using assms y_positivity inequality_transformation y_def
    sledgehammer
  then have "(9 * y^2 + 4) / y \<ge> 12"
    using assms inequality_transformation y_positivity y_def
    sledgehammer
  then show ?thesis
    using assms c1 y_def
    sledgehammer
qed

(* Problem

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.


 Solution

We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$.
This equals $a^2 + a - 10*11 = a^2 + a - 110$.

Conjectures

{(a - 10) * (a + 11) = a^2 - 10*a + 11*a - 110,
a^2 - 10*a + 11*a - 110 = a^2 + a - 110}
*)

lemma expansion_of_product:
  fixes a :: complex
  shows "(a - 10) * (a + 11) = a^2 - 10*a + 11*a - 110"
proof -
  show ?thesis
  \<proof>
qed

lemma simplification_of_terms:
  shows "a^2 - 10*a + 11*a - 110 = a^2 + a - 110"
proof -
  show ?thesis
    \<proof>
qed

theorem complex_number_identity:
  fixes a :: complex
  shows "(a - 10) * (a + 11) = a^2 + a - 110"
proof -
  have "a^2 - 10*a + 11*a - 110 = a^2 + a - 110"
    using expansion_of_product simplification_of_terms
    sledgehammer
  then show ?thesis
    using expansion_of_product
    sledgehammer
qed

(* Problem

For a positive real number x, show that $2 - \sqrt{2} \geq 2 - x - \frac{1}{2x}$.

Solution

First notice that $2x$ is positive.
It suffices to show $\sqrt{2} \leq x + \frac{1}{2x}$.
Let $y = \sqrt{2}$. $y*y = 2$.
Then $2x*x + 1 - 2x * \sqrt{2} = y*y * x*x + 1 - 2xy = (xy - 1)^2 \geq 0$.
Also notice that $2x*x + 1 - 2x * \sqrt{2} = 2x * (x + \frac{1}{2x} - \sqrt{2})$.
Therefore $x + \frac{1}{2x} - \sqrt{2} \geq 0$, given $2x > 0$.
Rearranging terms, we see that the required inequality holds.

Conjectures
{(2 * x) > 0}
*)

lemma c0: 
    fixes x :: real
    assumes "x > 0"
    shows "2 * x > 0"
proof -
    show ?thesis
    \<proof>
qed

theorem
  fixes x :: real
  assumes "x > 0"
  shows "2 - sqrt 2 \<ge> 2 - x - 1/ (2 * x)"
proof -
  (* First notice that $2x$ is positive. *)
  (* It suffices to show $\sqrt{2} \leq x + \frac{1}{2x}$. *)
  have "sqrt 2 \<le> x + 1 / (2 * x)"
  proof -
    (* Let $y = \sqrt{2}$. $y*y = 2$. *)
    define y where "y = sqrt 2"
    have c1: "2 = y * y"
      using c0 y_def
      sledgehammer
    (* Then $2x*x + 1 - 2x * \sqrt{2} = y*y * x*x + 1 - 2xy = (xy - 1)^2 \geq 0$. *)
    have "(2 * x) * x + 1 - (2 * x) * (sqrt 2) = (y * y * x * x) + 1 - (2 * x) * y"
      using c0 c1 y_def sledgehammer
    also have "... = (y*x) * (y*x) - 2 * (y*x) + 1" sledgehammer
    also have "... = (y*x - 1) * (y*x - 1)" sledgehammer
    also have "... \ge> 0" sledgehammer
    ultimately have c2: "(2 * x) * x + 1 - (2 * x) * (sqrt 2) \ge> 0" sledgehammer
    (* Also notice that $2x*x + 1 - 2x * \sqrt{2} = 2x * (x + \frac{1}{2x} - \sqrt{2})$. *)
    have "(2*x) * (x + 1/(2*x) - sqrt 2) = (2 * x) * x + (2 * x) * (1/(2*x)) - (2*x) * sqrt 2"
      sledgehammer
    also have "... = (2 * x) * x + 1 - (2*x) * sqrt 2" using c0 sledgehammer
    also have "... \ge> 0" using c0 c2 sledgehammer
    ultimately have "(2*x) * (x + 1/(2*x) - sqrt 2) \ge> 0" sledgehammer
    (* Therefore $x + \frac{1}{2x} - \sqrt{2} \geq 0$, given $2x > 0$. *)
    hence "x + 1/(2*x) - sqrt 2 \ge> 0" using c0
      sledgehammer
    (* Rearranging terms, we see that the required inequality holds. *)
    then show ?thesis sledgehammer
  qed
  then show ?thesis sledgehammer
qed

(*
{{problem}}
{{solution}}
{{conjectures}}
*)
"""

api_key = os.environ['MISTRAL_API_KEY']
model = "mistral-large-latest"


client = MistralClient(api_key=api_key)

problem="Let x be a real number. Show that x^2 + 2x + 1 > 0."
solution="The expression can be factored as (x + 1)^2. The square of a real number is always non-negative, so (x + 1)^2 > 0."
conjectures="{x^2 > 0}"

def prompt_lemmas(problem: str, solution: str, conjectures: str) -> str:
    completion = client.chat(
        model=model,
        messages=[
            # ChatMessage(role="system", content="You are a helpful assistant."),
            ChatMessage(role="user", content=load_template(prompt).render(
                problem=problem, 
                solution=solution, 
                conjectures=conjectures
                )
            ),
        ]
    )
    return completion.choices[0].message.content

if __name__=="__main__":
    print(prompt_lemmas(problem, solution, conjectures))
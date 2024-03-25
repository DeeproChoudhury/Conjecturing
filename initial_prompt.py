from mistralai.client import MistralClient
from mistralai.models.chat_completion import ChatMessage
import os
import sys

sys.path.append("/home/dc755/Conjecturing/")
sys.path.append("/home/dc755/Conjecturing/conjecture_generation/")
sys.path.append("/home/dc755/Conjecturing/conjecture_generation/src/")
WORK_DIR = os.getcwd()
print(sys.path)
from utils.create import load_template
from utils.json_utils import write_to_new_json, load_json_as_list
from conjecture_generation.src.domain import Domain
from conjecture_generation.src.func_parameterization import FunctionParameterization
from conjecture_generation.src.functions import exponential_box
from conjecture_generation.src.conj_gen import find_new_conj, sgd_signum_loss, save_conj
from initial_functions import poly_box
import dsp_functions

prompt = """Translate the informal solution into a sketch of the
formal Isabelle proof. Add `sledgehammer` in the sketch whenever
possible. `sledgehammer` will be used to call the automated Sledgehammer prover. 
Some conjectures with underscores in the variable names will be specified in the prompt, in the form of python dictionaries
with keys labelled either 'initial conjecture', 'conjecture' or 'final conjecture'.
Translate them into their formal Isabelle form
as lemmas, but do not prove them. When calling sledgehammer, use the lemmas as assumptions.
Here are some examples:

(* Problem:\n\n
Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. 
Show that it is 12.

Solution:\n\n
Let $y = x \\sin x$. It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}.\n
It is trivial to see that $y > 0$. \nThen one can multiply both sides by $y$ and 
it suffices to show $12y \\leq 9y^2 + 4$.\nThis can be done by the sum of squares method. 

Conjectures: 
{'initial_conjecture' : '(9 * y_1^2 + 4) / y_1 >= 12', 'final_conjecture': y_1 * sin y_1 > 0}
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

(* Problem:

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.


Solution:

We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$.
This equals $a^2 + a - 10*11 = a^2 + a - 110$.

Conjectures:

{'initial_conjecture' : '(a_1 - 10) * (a_1 + 11) = a_1^2 - 10*a_1 + 11*a_1 - 110',
'final_conjecture' : 'a_1^2 - 10*a_1 + 11*a_1 - 110 = a_1^2 + a_1 - 110'}
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

(* Problem:

For a positive real number x, show that $2 - \sqrt{2} \geq 2 - x - \frac{1}{2x}$.

Solution:

First notice that $2x$ is positive.
It suffices to show $\sqrt{2} \leq x + \frac{1}{2x}$.
Let $y = \sqrt{2}$. $y*y = 2$.
Then $2x*x + 1 - 2x * \sqrt{2} = y*y * x*x + 1 - 2xy = (xy - 1)^2 \geq 0$.
Also notice that $2x*x + 1 - 2x * \sqrt{2} = 2x * (x + \frac{1}{2x} - \sqrt{2})$.
Therefore $x + \frac{1}{2x} - \sqrt{2} \geq 0$, given $2x > 0$.
Rearranging terms, we see that the required inequality holds.

Conjectures:
{'initial_conjecture' : '(2 * x_1) > 0'}
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
Problem:

{{problem}}

Solution:

{{solution}}

Conjectures:

{{conjectures}}
*)
"""

with open('labelled_prompt_2.txt', 'r') as file:
    prompt = file.read()

api_key = os.environ['MISTRAL_API_KEY']
model = "mistral-large-latest"


client = MistralClient(api_key=api_key)

problem="Let $x$ be a real number. Show that $x^2 + 2x + 1 \geq 0$."
solution="The expression can be factored as $(x + 1)^2$. The square of a real number is always non-negative, so $(x + 1)^2 \geq 0$."
conjectures="{conjecture : x_1^2 >= 0, conjecture: (x + 1)^2 >= 0}"

# problem="Let $x$ be a real number. Prove that $1 \leq \frac{1}{2}(\sin x + 3) \leq 2$."
# solution="We know by definition that $-1 \leq \sin x \leq 1$, so we start with that and do some rearranging. Adding 3 gives us $2 \leq \sin x + 3 \leq 4$. Dividing by 2 gives us $1 \leq \frac{1}{2}(\sin x + 3) \leq 2."

def prompt_lemmas(problem: str, solution: str, conjectures: str, functions=None) -> str:
    if functions is not None:
        conjectures = conjectures + functions

    print("conjectures: ", conjectures)

    with open("prompt_example", "w") as file:
        file.write(load_template(prompt).render(problem=problem, solution=solution, conjectures=conjectures))
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
    with open("response_example_2.txt", "w") as file:
        file.write(completion.choices[0].message.content)
    return completion.choices[0].message.content

# local_function_box = [x, x^2]

def local_save_conj(initial_conj: str, final_conj: str = None, sig_val=0):
    if final_conj is not None:
        data_dictionary = {
            # "initial_conjecture": initial_conj + " > 0",
            "conjecture": final_conj.replace("**", "^") + " > 0" if sig_val >= 0 else final_conj.replace("**", "^") + " < 0",
        }
    else:
        data_dictionary = {"conjecture": initial_conj.replace("**", "^") + " > 0"}

    return write_to_new_json(data_dictionary, directory=WORK_DIR, filename_prefix="conjectures")

domain = Domain(
    func_box=poly_box,
    max_degree=1,
    latent_dim=1,
    evaluation_dimension=10,
    testset_size=100,
)
if __name__=="__main__":
    
    file_saved = []
    [x_var, combs, eval_point] = domain.generate_evaluation_domain_continuous(
        pnt_start=-3, pnt_end=3, n_pnts=100
    )

    [y_symbs, num_pars, func_evals, eval_data] = domain.generate_hypothesis_space(
        vars=x_var, cmbs=combs, eval_points=eval_point
    )

    func_param = FunctionParameterization(num_pars=num_pars, y_symbs=y_symbs)
    print(f"Initial θ vector is: {func_param.θ}")

    no_of_tries = 10000
    counter = no_of_tries
    while counter > 0:
        [initial_conj, initial_loss, flag, sig_val] = find_new_conj(
            num_pars=num_pars,
            eval_data=eval_data,
            y_symbs=y_symbs,
            func_evals=func_evals,
        )
        print(
            f"initial conj number: {no_of_tries - counter} is: {initial_conj}..associated loss is: {initial_loss}"
        )
        initial_conj = str(initial_conj)
        if not flag:
            file_saved.append(local_save_conj(initial_conj=initial_conj))
            print("this is the file saved", file_saved)
            counter -= 1
        else:
            break

    if flag:
        print("Actual learning needed")
        [final_conj, final_loss, not_contains_zero] = sgd_signum_loss(
            y_symbs=y_symbs,
            training_data=eval_data,
            func_param=func_param,
            sig_val=sig_val,
            batch_prct=0.1,
            num_epochs=100,
            θ_differential=100,
            learn_rate=10,
            initial_loss=initial_loss,
            loss_type="signum",
            comp_number=1,
            num_pars=num_pars,
        )

        sub_list = zip(y_symbs, func_evals)
        final_conj = final_conj.subs(sub_list)
        final_conj = str(final_conj)
        greater_than, less_than = [">", "<"]
        if not not_contains_zero:
          if sig_val > 0:
            print(f"The final conjecture is: {final_conj} >= 0")
          else:
            final_conj = final_conj.replace(">", "<")
            print(f"The final conjecture is: {final_conj} <= 0")

        if sig_val > 0:
          print(f"The final conjecture is: {final_conj} > 0")
        else:
          final_conj = final_conj.replace(">", "<")
          print(f"The final conjecture is: {final_conj} < 0")

        file_saved.append(local_save_conj(initial_conj=initial_conj, final_conj=final_conj, sig_val=sig_val))

        print(f"Found {no_of_tries - counter + 1} conjectures in total!")

    else:
        print("Couldn't find conjecture needing training but saved 100 conjectures!")

    # conjectures = load_json_as_list(file_saved)
    # conjectures = []
    # for file in file_saved:
    #     conjectures.append(load_json_as_list(file))

    os.environ['PISA_PATH'] = '/home/dc755/Portal-to-ISAbelle/src/main/python'

    checker = dsp_functions.Checker(
        working_dir='/home/dc755/Isabelle2022/src/HOL/Examples',
        isa_path='/home/dc755/Isabelle2022',
        theory_file='/home/dc755/Isabelle2022/src/HOL/Examples/Interactive.thy',
        port=8000
    )
    for _ in range(5):
      print(prompt_lemmas(problem, solution, conjectures))


      with open('response_example_2.txt', 'r') as file:
          response = file.read()

      result = checker.check(response)

      print("\n==== Success: %s" % result['success'])
      print("--- Complete proof:\n%s" % result['theorem_and_proof'])

      if result['success']:
          print("Proof successful!")
          break
      else:
          print("Proof failed. Trying again...")
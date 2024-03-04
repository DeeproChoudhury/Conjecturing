from mistralai.client import MistralClient
from mistralai.models.chat_completion import ChatMessage
import os

prompt = """Translate the informal solution into a sketch of the
formal Isabelle proof. Add `sledgehammer` in the sketch whenever
possible. `sledgehammer` will be used to call the automated Sledgehammer prover. 
Here are some examples:
"""

api_key = os.environ['MISTRAL_API_KEY']
model = "mistral-large-latest"


client = MistralClient(api_key=api_key)

def prompt_lemmas() -> str:
    completion = client.chat(
        model=model,
        messages=[
            # ChatMessage(role="system", content="You are a helpful assistant."),
            ChatMessage(role="user", content="I need help with a lemma.")
        ]
    )
    return completion.choices[0].message.content

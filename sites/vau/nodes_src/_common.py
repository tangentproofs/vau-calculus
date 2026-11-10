# Shared helpers for the vau explainer nodes. Files starting with "_" define no nodes
# (engine/tools/write_nodes.py skips them). Every node file defines NODES.
THESIS = "https://web.cs.wpi.edu/~jshutt/dissertation/etd-090110-124904-Shutt-Dissertation.pdf"
NEPLS = "https://web.cs.wpi.edu/~jshutt/jns-nepls07.txt"
DALE_FEXPR = "https://dalnefre.com/wp/2011/11/fexpr-the-ultimate-lambda/"
DALE_EXT = "https://dalnefre.com/wp/2011/12/semantic-extensibility-with-vau/"
DALE_ACTORS = "https://dalnefre.com/wp/2012/02/implementing-actors-in-kernel/"


def thesis(page, label):
    """Markdown link to one page of Shutt's thesis PDF (page = PDF page number, not printed page)."""
    return f"[{label}]({THESIS}#page={page})"


def make(nodes):
    def node(id, title, summary, body, quiz, caveats=(), widgets=None):
        nodes.append(dict(id=id, title=title, summary=summary, body=body, quiz=quiz, caveats=list(caveats), widgets=widgets))
    return node


def q(text, choices, answer, explain):
    return {"q": text, "type": "choice", "choices": choices, "answer": answer, "explain": explain}

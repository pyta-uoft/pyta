const defaultCode = `"""This file illustrates basic usage of PythonTA's code analysis.
"""


def add_two(x: int, y: int) -> int:
    """Return the sum of x and y.

    PythonTA's analysis of this code will report three issues:

    1. A missing return statement (a logical error)
    2. Missing whitespace around the + (a formatting issue)
    3. The presence of a print call (a code style issue)
    """
    result = x+y
    print(result)
`

document.getElementById("codeblock").value = defaultCode

const submitButton = document.getElementById("submitButton")
const outputContainer = document.getElementById("output-container")
const codeblock = document.getElementById("codeblock")

const pyodideWorker = new Worker("worker.js", { type: "module" })

let lastId = 1

function requestResponse(worker, msg) {
  return new Promise((resolve) => {
    const idWorker = lastId++

    function listener(event) {
      if (event.data?.id !== idWorker) {
        return
      }
      worker.removeEventListener("message", listener)
      resolve(event.data)
    }

    worker.addEventListener("message", listener)
    worker.postMessage({ id: idWorker, ...msg })
  })
}

async function initialize() {
  submitButton.disabled = true
  const response = await requestResponse(pyodideWorker, { type: "INIT" })
  if (response.type === "READY") {
    submitButton.disabled = false
    submitButton.innerText = "Check Code!"
  } else {
    console.error("Failed to initialize Pyodide:", response.error)
  }
}

initialize()

submitButton.addEventListener("click", async () => {
  const codeInput = codeblock.value

  submitButton.disabled = true
  submitButton.innerText = "Analyzing Code..."
  outputContainer.innerHTML = '<div class="placeholder-text">Analyzing...</div>'

  const response = await requestResponse(pyodideWorker, {
    type: "CHECK_CODE",
    code: codeInput,
  })

  if (response.type === "RESULT") {
    const iframe = document.createElement("iframe")
    iframe.srcdoc = response.html
    outputContainer.innerHTML = ""
    outputContainer.appendChild(iframe)
  } else if (response.type === "ERROR") {
    console.error(response.error)
    outputContainer.innerHTML = `<div class="error-text">An error occurred while analyzing the code:<br><br>${response.error}</div>`
  }

  submitButton.disabled = false
  submitButton.innerText = "Check Code!"
})

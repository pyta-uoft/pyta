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

let checkAll = () => {}

const submitButton = document.getElementById("submitButton")
const outputContainer = document.getElementById("output-container")
const codeblock = document.getElementById("codeblock")

submitButton.addEventListener("click", async () => {
  const codeInput = codeblock.value

  try {
    const reportHtml = checkAll(codeInput)
    outputContainer.innerHTML = `<iframe srcdoc="${reportHtml}"></iframe>`
  } catch (err) {
    console.error(err)
    outputContainer.innerHTML = `<div style="color: red;">An error occurred while analyzing the code:<br><br>${err.message}</div>`
  }
})

async function initialize() {
  let pyodide = await loadPyodide({
    packages: ["micropip"],
  })

  await pyodide.runPythonAsync(`
        import micropip
        mock_watchdog_modules = {
            "watchdog": "",
            "watchdog.events": "class FileSystemEventHandler: pass",
            "watchdog.observers": "class Observer: pass",
        }
        micropip.add_mock_package("watchdog", "6.0.0", modules=mock_watchdog_modules)
        await micropip.install("python-ta")
    `)

  const generateReport = pyodide.runPython(`
        import python_ta
        def generate_report():
            python_ta.check_all("code_input.py", output="report.html")
        generate_report
    `)

  checkAll = (codeInput) => {
    pyodide.FS.writeFile("code_input.py", codeInput)
    generateReport()
    const htmlOutput = pyodide.FS.readFile("report.html", { encoding: "utf8" })
    const safeHtmlOutput = htmlOutput.replace(/"/g, "&quot;")
    return safeHtmlOutput
  }

  submitButton.disabled = false
  submitButton.innerText = "Check Code!"
}

initialize()

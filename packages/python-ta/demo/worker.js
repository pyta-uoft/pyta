import { loadPyodide } from "https://cdn.jsdelivr.net/pyodide/v314.0.0/full/pyodide.mjs"

let pyodideReadyPromise

async function loadPyodideAndPackages() {
  self.pyodide = await loadPyodide()
  await self.pyodide.loadPackage(["micropip"])

  await self.pyodide.runPythonAsync(`
      import micropip
      mock_watchdog_modules = {
          "watchdog": "",
          "watchdog.events": "class FileSystemEventHandler: pass",
          "watchdog.observers": "class Observer: pass",
      }
      micropip.add_mock_package("watchdog", "6.0.0", modules=mock_watchdog_modules)
      await micropip.install("python-ta")
  `)

  self.generateReport = (codeInput) => {
    pyodide.FS.writeFile("code_input.py", codeInput)

    return pyodide.runPython(`
        import python_ta
        import io
        buf = io.StringIO()
        python_ta.check_all("code_input.py", output=buf)
        buf.getvalue()
    `)
  }
}

pyodideReadyPromise = loadPyodideAndPackages()

self.onmessage = async (event) => {
  const { id, type, code: codeInput } = event.data
  if (type === "INIT") {
    try {
      await pyodideReadyPromise
      self.postMessage({ id, type: "READY" })
    } catch (error) {
      self.postMessage({ id, type: "ERROR", error: error.message })
    }
  } else if (type === "CHECK_CODE") {
    try {
      await pyodideReadyPromise
      const reportHtml = self.generateReport(codeInput)
      self.postMessage({ id, type: "RESULT", html: reportHtml })
    } catch (error) {
      self.postMessage({ id, type: "ERROR", error: error.message })
    }
  }
}

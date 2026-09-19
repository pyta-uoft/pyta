function initializeTheme() {
  const savedTheme = localStorage.getItem("pyta-theme")
  const prefersDark = window.matchMedia("(prefers-color-scheme: dark)").matches
  const theme = savedTheme || (prefersDark ? "dark" : "light")

  document.documentElement.setAttribute("data-theme", theme)
}

function toggleTheme() {
  const currentTheme = document.documentElement.getAttribute("data-theme")
  const newTheme = currentTheme === "dark" ? "light" : "dark"

  document.documentElement.setAttribute("data-theme", newTheme)
  localStorage.setItem("pyta-theme", newTheme)
}

// Initialize the user's theme when the page loads
document.addEventListener("DOMContentLoaded", () => {
  initializeTheme()
  initializePins()

  // Theme toggle event listener
  const themeToggle = document.getElementById("theme-toggle")
  if (themeToggle) {
    themeToggle.addEventListener("click", toggleTheme)
  }
})

window
  .matchMedia("(prefers-color-scheme: dark)")
  .addEventListener("change", (e) => {
    if (!localStorage.getItem("pyta-theme")) {
      const theme = e.matches ? "dark" : "light"
      document.documentElement.setAttribute("data-theme", theme)
    }
  })

/* A pin marks one error type within one file. */

const PIN_STORAGE_KEY = "pyta-pinned-errors"
// NUL cannot appear in a filename, so it cannot collide with one.
const PIN_SEPARATOR = "\u0000"

let pinnedKeys = new Set()

function loadPinnedKeys() {
  try {
    const raw = localStorage.getItem(PIN_STORAGE_KEY)
    if (!raw) {
      return new Set()
    }
    const parsed = JSON.parse(raw)
    if (!Array.isArray(parsed)) {
      return new Set()
    }
    return new Set(parsed.filter((key) => typeof key === "string"))
  } catch (err) {
    // Storage may be unavailable (private browsing, blocked site data) or hold
    // malformed JSON. Start with no pins rather than breaking the report.
    return new Set()
  }
}

function savePinnedKeys() {
  try {
    localStorage.setItem(
      PIN_STORAGE_KEY,
      JSON.stringify(Array.from(pinnedKeys)),
    )
  } catch (err) {
    // Pinning still works for this page view even if it cannot be persisted.
  }
}

function pinKeyFor(instance) {
  const section = instance.closest("section[data-filename]")
  if (!section || !instance.dataset.msgId) {
    return null
  }
  return section.dataset.filename + PIN_SEPARATOR + instance.dataset.msgId
}

function isPinnedOnly() {
  return document.body.classList.contains("pinned-only")
}

/* Hide everything that is not pinned, then hide any group left empty. */
function applyPinFilter() {
  const pinnedOnly = isPinnedOnly()

  document.querySelectorAll(".error-instance").forEach((instance) => {
    instance.hidden = pinnedOnly && !instance.classList.contains("pinned")
  })
  document.querySelectorAll("article.error-output").forEach((article) => {
    article.hidden =
      pinnedOnly && !article.querySelector(".error-instance:not([hidden])")
  })
  document.querySelectorAll("main > section").forEach((section) => {
    section.hidden =
      pinnedOnly && !section.querySelector("article.error-output:not([hidden])")
  })
  document.querySelectorAll("[data-pin-ref]").forEach((entry) => {
    entry.hidden = pinnedOnly && !entry.classList.contains("pinned")
  })
  // Applies to both the per-file and per-category groups in the sidebar.
  document.querySelectorAll(".sidebar li.collapsible").forEach((group) => {
    group.hidden =
      pinnedOnly && !group.querySelector("[data-pin-ref]:not([hidden])")
  })
}

function updatePinControls(count) {
  const filter = document.getElementById("pin-filter")
  const summary = document.getElementById("pin-summary")
  const summaryText = document.getElementById("pin-summary-text")

  if (filter) {
    filter.hidden = count === 0
    // Filtering to an empty report would leave no way back, so release the
    // filter when the last pin in view is removed.
    if (count === 0 && filter.getAttribute("aria-pressed") === "true") {
      filter.setAttribute("aria-pressed", "false")
      document.body.classList.remove("pinned-only")
    }
  }
  if (summary) {
    summary.hidden = count === 0
  }
  if (summaryText) {
    summaryText.textContent =
      count === 1 ? "1 pinned error" : count + " pinned errors"
  }
}

function renderPinState() {
  let count = 0

  document.querySelectorAll(".error-instance").forEach((instance) => {
    const key = pinKeyFor(instance)
    const pinned = key !== null && pinnedKeys.has(key)
    if (pinned) {
      count += 1
    }

    instance.classList.toggle("pinned", pinned)

    const button = instance.querySelector(".pin-toggle")
    if (button) {
      const label = pinned ? "Unpin this error" : "Pin this error"
      button.setAttribute("aria-pressed", String(pinned))
      button.setAttribute("aria-label", label)
      button.setAttribute("title", label)
    }

    const entry = document.querySelector('[data-pin-ref="' + instance.id + '"]')
    if (entry) {
      entry.classList.toggle("pinned", pinned)
    }
  })

  updatePinControls(count)
  applyPinFilter()
}

function togglePin(instance) {
  const key = pinKeyFor(instance)
  if (key === null) {
    return
  }
  if (pinnedKeys.has(key)) {
    pinnedKeys.delete(key)
  } else {
    pinnedKeys.add(key)
  }
  savePinnedKeys()
  renderPinState()
}

/* Unpin only what this report shows, so pins for files checked separately survive. */
function clearPinsInReport() {
  document.querySelectorAll(".error-instance").forEach((instance) => {
    const key = pinKeyFor(instance)
    if (key !== null) {
      pinnedKeys.delete(key)
    }
  })
  savePinnedKeys()
  renderPinState()
}

function initializePins() {
  pinnedKeys = loadPinnedKeys()

  document.body.addEventListener("click", (event) => {
    const button = event.target.closest(".pin-toggle")
    if (!button) {
      return
    }
    const instance = button.closest(".error-instance")
    if (instance) {
      togglePin(instance)
    }
  })

  const filter = document.getElementById("pin-filter")
  if (filter) {
    filter.addEventListener("click", () => {
      const active = document.body.classList.toggle("pinned-only")
      filter.setAttribute("aria-pressed", String(active))
      filter.setAttribute(
        "title",
        active ? "Show all errors" : "Show only pinned errors",
      )
      filter.setAttribute(
        "aria-label",
        active ? "Show all errors" : "Show only pinned errors",
      )
      applyPinFilter()
    })
  }

  const clearButton = document.getElementById("clear-pins")
  if (clearButton) {
    clearButton.addEventListener("click", clearPinsInReport)
  }

  renderPinState()
}

// Existing collapsible functionality
document.body.addEventListener("click", (event) => {
  const slider = event.target.closest(".slider")
  if (slider) {
    const parent = slider.parentElement
    const elem = parent?.nextElementSibling

    if (elem) {
      toggleElement(elem)
    }

    Array.from(slider.children).forEach((child) => {
      if (child.nodeType === 1) {
        child.classList.toggle("collapsed")
      }
    })
  }
})

document
  .querySelectorAll(".sidebar li.collapsible > button")
  .forEach((button) => {
    button.addEventListener("click", () => {
      let collapsible = button.closest(".collapsible")

      if (collapsible) {
        const ul = collapsible.querySelector("ul")
        if (ul) {
          ul.style.display = ul.style.display === "none" ? "block" : "none"
        }
      }

      const svg = button.querySelector("svg")
      if (svg) {
        svg.classList.toggle("collapsed")
      }
    })
  })

/* Function for animating a collapsible element, adapted from
 * https://carlanderson.xyz/how-to-animate-on-height-auto/
 */
function toggleElement(elem) {
  const expanded = elem.classList.contains("expanded")
  elem.style.height = ""
  elem.style.transition = "none"

  // Set the start height to begin the transition
  const startHeight = window.getComputedStyle(elem).height

  if (expanded) {
    elem.style.height = startHeight
  }

  elem.classList.toggle("hide-and-maintain-width")
  elem.classList.toggle("expanded")

  let height
  if (expanded) {
    height = 0
  } else {
    height = window.getComputedStyle(elem).height
    elem.style.height = startHeight
  }

  // wait until the next frame so that everything has time to update before starting the transition
  requestAnimationFrame(() => {
    elem.style.transition = ""

    requestAnimationFrame(() => {
      elem.style.height = height
    })
  })

  // Clear the saved height values after the transition
  elem.addEventListener("transitionend", () => {
    elem.style.height = ""
    elem.removeEventListener("transitionend", arguments.callee)
  })
}

const socket = new WebSocket("ws://localhost:{{ port }}/ws")

socket.onmessage = (event) => {
  if (event.data === "reload") {
    window.location.reload()
  }
}

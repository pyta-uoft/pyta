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

document.querySelectorAll(".sidebar button").forEach((button) => {
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

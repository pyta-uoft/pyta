$("body").on("click", ".slider", function () {
  let elem = $(this).parent().next()[0]
  toggleElement(elem)
  $(this).children().toggleClass("collapsed")
})

$(".sidebar button").click(function () {
  $(this).closest(".collapsible").children("ul").toggle()
  $(this).children("svg").toggleClass("collapsed")
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

$("body").on("click", ".slider", function () {
    $(this).parent().next().toggleClass("hide-and-maintain-width");
});

function toggleClosestCollapsible() {  
    $(this).closest(".collapsible").children("ul").toggle();
    $(this).children("svg").toggleClass("collapsed");
};

$(".sidebar button").click(toggleClosestCollapsible);
$(".sidebar button").keydown(function(event) {
    const spacePressed = event.key === " ";
    const enterPressed = event.key === "Enter";
    if (spacePressed || enterPressed) {
        event.preventDefault();
        $(this).trigger("click");
    }
})

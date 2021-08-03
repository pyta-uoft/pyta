$("body").on("click", ".slider", function () {
    $(this).parent().next().toggleClass("hide-and-maintain-width");
});

$(".sidebar button").click(function () {  
    $(this).closest(".collapsible").children("ul").toggle();
    $(this).children("svg").toggleClass("collapsed");
});

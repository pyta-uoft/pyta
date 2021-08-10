$("body").on("click", ".slider", function () {
    $(this).parent().next().toggleClass("hide-and-maintain-width");
    $(this).children().toggleClass("collapsed");
});

$(".sidebar button").click(function () {  
    $(this).closest(".collapsible").children("ul").toggle();
    $(this).children("svg").toggleClass("collapsed");
});

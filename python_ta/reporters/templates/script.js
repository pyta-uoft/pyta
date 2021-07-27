$("body").on("click", ".slider", function () {
    $(this).parent().next().toggleClass("hide-and-maintain-width");
    $(this).children().toggleClass("collapsed");
});

//$(".collapsible").on("click", ".collapse-trigger", function (evt) {
//    $(this).closest(".collapsible").children("ul").toggle()
//    $(this).toggleClass("collapsed")
//});
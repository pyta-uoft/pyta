$("body").on("click", ".slider", function () {
    $(this).parent().next().slideToggle(500, function () {});
});
